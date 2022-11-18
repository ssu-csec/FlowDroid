package soot.jimple.infoflow.android;

import org.json.simple.JSONArray;
import org.json.simple.JSONObject;
import org.json.simple.parser.JSONParser;
import org.json.simple.parser.ParseException;
import soot.*;
import soot.javaToJimple.LocalGenerator;
import soot.jimple.*;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.JastAddJ.BooleanType;

import java.io.*;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Stream;

public class AngrCallgraph {
    static String dummyNativeClassName = "DummyNative";
    static SootClass dummyNativeClass;
    static List<Local> allocatedLocals;
    static Local dummyLocal;
    static CallGraph cg;

    public static CallGraph newCallgraph(InfoflowAndroidConfiguration config) {
        String jsonPath = config.getAnalysisFileConfig().getAngrJsonFile();
        String sourceSinkPath = config.getAnalysisFileConfig().getSourceSinkFile();

        byte[] jsonBytes;
        try {
            assert jsonPath != null;
            jsonBytes = Files.readAllBytes(Paths.get(jsonPath));
        } catch (IOException ioe){
            ioe.printStackTrace();
            return null;
        }

        String jsonStr = new String(jsonBytes);
        JSONParser jp = new JSONParser();
        JSONArray nodesJson = null;
        JSONArray edgesJson = null;
        JSONArray nativeSourcesJson = null;
        try {
            JSONObject jo = (JSONObject) jp.parse(jsonStr);
            nodesJson = (JSONArray) jo.get("nodes");
            edgesJson = (JSONArray) jo.get("edges");
            nativeSourcesJson = (JSONArray) jo.get("native_sources");
        } catch(ParseException ignored){
        }

        cg = Scene.v().getCallGraph();
        if (nodesJson != null) {
            loadDummyNodes(nodesJson);
        }
        appendSourcesAndSinks(nativeSourcesJson, sourceSinkPath);
        //CallGraph cg = new CallGraph();
        List<Edge> edges = parseEdges(edgesJson);
        assert edges != null;

        for (Edge edge : edges) {
            cg.addEdge(edge);
        }

        return cg;
    }
    public static void loadDummyNodes(JSONArray nodes){
        if(nodes == null){
            return;
        }

        dummyNativeClass = Scene.v().getSootClassUnsafe(dummyNativeClassName);
        dummyNativeClass.setModifiers(9);
        dummyNativeClass.setApplicationClass();

        for (Object node : nodes) {
            JSONObject jo = (JSONObject) node;
            // get method from class with params and ret
            SootMethod sootMethod = getMethod(jo);

            if(sootMethod==null){
                continue;
            }

            sootMethod.setModifiers(Modifier.PUBLIC);       // To avoid concrete

            // load body
            allocatedLocals = new LinkedList<>();
            JimpleBody body = Jimple.v().newBody();
            body.setMethod(sootMethod);
            loadBody(jo, body, sootMethod);

            sootMethod.setActiveBody(body);
        }
    }
    public static SootMethod getMethod(JSONObject jo){
        String className = (String) jo.get("class");
        String methodName = (String) jo.get("name");
        String retType = (String) jo.get("ret");
        String params = (String) jo.get("params");
        String subSig = retType + " " + methodName + params;
        SootClass sootClass;

        if(Scene.v().containsClass(className)) {
            sootClass = Scene.v().getSootClass(className);
        }
        else{
            sootClass = Scene.v().makeSootClass(className);
            sootClass.setModifiers(9);
            sootClass.setApplicationClass();
        }

        SootMethod sootMethod = sootClass.getMethodUnsafe(subSig);

        if(sootMethod==null && methodName.equals("JNI_OnLoad")){
            List<Type> paramTypes = new LinkedList<Type>();
            sootMethod = Scene.v().makeSootMethod(methodName, paramTypes, VoidType.v());
            sootMethod.setModifiers(Modifier.PUBLIC + Modifier.STATIC);
            sootClass.addMethod(sootMethod);
        }
        return sootMethod;
    }
    public static void loadBody(JSONObject jo, JimpleBody body, SootMethod sootMethod){
        LocalGenerator lg = new LocalGenerator(body);
        List<JSONObject> stmtInfoList = (List<JSONObject>) jo.get("body");
        List<Local> localList = new LinkedList<Local>();

        for (JSONObject stmtInfo : stmtInfoList){
            Stmt stmt = resolveStmt(stmtInfo, body, lg);

            if(stmt!=null)
                body.getUnits().add(stmt);
        }
    }
    public static Stmt resolveStmt(JSONObject stmtInfo, Body body, LocalGenerator localGenerator){
        String stmtType = (String) stmtInfo.get("stmt_type");
        Stmt stmt;
        switch(stmtType){
            case "identity":
                Local identityLocal = (Local) resolveLeftValue((JSONObject) stmtInfo.get("local"), body, localGenerator);
                Ref identityRef = (Ref) resolveValue((JSONObject) stmtInfo.get("param_ref"), body, localGenerator);
                stmt = Jimple.v().newIdentityStmt(identityLocal, identityRef);
                break;
            case "assign":
                Value rightOp = resolveValue((JSONObject) stmtInfo.get("right_op"), body, localGenerator);
                Value leftOp = resolveLeftValue((JSONObject) stmtInfo.get("left_op"), body, localGenerator);
                stmt = Jimple.v().newAssignStmt(leftOp, rightOp);

                if(rightOp instanceof InvokeExpr) {
                    SootMethod src = body.getMethod();
                    SootMethod tgt = ((InvokeExpr) rightOp).getMethod();
                    addEdgeForInvoke(stmt, src, tgt, Kind.STATIC);
                }
                break;
            case "dummy":
                Value rightDummyOp = resolveValue((JSONObject) stmtInfo.get("right_op"), body, localGenerator);
                if(rightDummyOp==null){
                    stmt=null;
                }
                else{
                    Value leftDummyOp = resolveLeftValue((JSONObject) stmtInfo.get("left_op"), body, localGenerator);
                    stmt = Jimple.v().newAssignStmt(leftDummyOp, rightDummyOp);

                    if(rightDummyOp instanceof InvokeExpr) {
                        SootMethod src = body.getMethod();
                        SootMethod tgt = ((InvokeExpr) rightDummyOp).getMethod();
                        addEdgeForInvoke(stmt, src, tgt, Kind.STATIC);
                    }
                    dummyLocal = (Local) leftDummyOp;
                }
                break;
            case "invoke":
                InvokeExpr invokeExpr = resolveInvokeExpr(stmtInfo, body, localGenerator);
                stmt = Jimple.v().newInvokeStmt(invokeExpr);

                SootMethod src = body.getMethod();
                SootMethod tgt = invokeExpr.getMethod();
                Kind kind;
                if(tgt.isStatic()){
                    kind = Kind.STATIC;
                }else{
                    kind = Kind.VIRTUAL;
                }
                addEdgeForInvoke(stmt, src, tgt, kind);
                break;
            case "return":
                Value op = resolveValue((JSONObject) stmtInfo.get("local"), body, localGenerator);
                stmt = Jimple.v().newReturnStmt(op);
                break;
            case "return_void":
                stmt = Jimple.v().newReturnVoidStmt();
                break;
            default:
                stmt = Jimple.v().newNopStmt();
        }

        return stmt;
    }
    public static void addEdgeForInvoke(Stmt stmt, SootMethod src, SootMethod tgt, Kind kind) {
        Edge edge = new Edge(src, stmt, tgt, kind);
        cg.addEdge(edge);
    }
    public static InvokeExpr resolveInvokeExpr(JSONObject exprInfo, Body body, LocalGenerator localGenerator) {
        String signature = (String) exprInfo.get("callee");
        SootMethod calleeMethod = Scene.v().grabMethod(signature);

        if (calleeMethod == null) {
            calleeMethod = makeMethodBySignature(signature);
            calleeMethod.setModifiers(Modifier.PUBLIC + Modifier.STATIC);
            calleeMethod.setPhantom(true);

            String[] splitStr = signature.substring(1).split(":");
            String class_name = splitStr[0];
            SootClass sootClass = Scene.v().getSootClassUnsafe(class_name);

            if(sootClass == null) {
                sootClass = Scene.v().getSootClassUnsafe(class_name);
            }

            sootClass.addMethod(calleeMethod);
        }

        List<Value> args = new LinkedList<>();
        Value value;
        for(Object arg: (JSONArray) exprInfo.get("args")){
            if (arg == null) {
                value = dummyLocal;
            } else {
                    value = getLocal(body, ((Long) arg).intValue());
            }
            args.add(value);
        }
        InvokeExpr expr;
        SootMethodRef ref = calleeMethod.makeRef();

        if(ref.isStatic()){
            expr = Jimple.v().newStaticInvokeExpr(calleeMethod.makeRef(), args);
        }
        else{
            Local tmpRef = localGenerator.generateLocal(calleeMethod.getReturnType());
            expr = Jimple.v().newVirtualInvokeExpr(tmpRef, ref, args);
        }

        return expr;
    }
    public static Value resolveValue(JSONObject valueInfo, Body body, LocalGenerator localGenerator) {
        String valueType = (String) valueInfo.get("stmt_type");
        Value value;
        switch (valueType) {
            case "local":
                value = resolveLocal(valueInfo, body, localGenerator);
                break;
            case "const":
                value = resolveConstant(valueInfo);
                break;
            case "boolean":
                value = BooleanType.emitConstant((boolean) valueInfo.get("value"));
                break;
            case "byte":
                value = IntConstant.v(((Long) valueInfo.get("value")).intValue());
                break;
            case "char":
                value = IntConstant.v(((Long) valueInfo.get("value")).intValue());
                break;
            case "short":
                value = IntConstant.v(((Long) valueInfo.get("value")).intValue());
                break;
            case "int":
                value = IntConstant.v(((Long) valueInfo.get("value")).intValue());
                break;
            case "long":
                value = LongConstant.v(((Long) valueInfo.get("value")).intValue());
                break;
            case "float":
                value = FloatConstant.v(((Long) valueInfo.get("value")).intValue());
                break;
            case "double":
                value = DoubleConstant.v(((Long) valueInfo.get("value")).intValue());
                break;
            case "string":
                value = StringConstant.v((String) valueInfo.get("value"));
                break;
            case "new":
                value = newObject(((String) valueInfo.get("type")));
                break;
            case "invoke":
                value = resolveInvokeExpr(valueInfo, body, localGenerator);
                break;
            default:
                value = resolveRef(valueInfo, body);
                break;
        }
        return value;
    }
    public static Value resolveConstant(JSONObject constInfo) {
        String valueType = (String) constInfo.get("type");
        if(valueType.equals("java.lang.String")) {
            return StringConstant.v((String) constInfo.get("value"));
        }
        else{
            return null;
        }
    }

    public static Value resolveLeftValue(JSONObject valueInfo, Body body, LocalGenerator localGenerator) {
        String valueType = (String) valueInfo.get("stmt_type");
        Value value;
        switch (valueType) {
            case "local":
                value = resolveLeftLocal(valueInfo, body, localGenerator);
                break;
            case "int":
                value = IntConstant.v(((Long) valueInfo.get("value")).intValue());
                break;
            case "long":
                value = LongConstant.v(((Long) valueInfo.get("value")));
                break;
            case "float":
                value = FloatConstant.v(((Long) valueInfo.get("value")).floatValue());
                break;
            case "double":
                value = DoubleConstant.v(((Long) valueInfo.get("value")).doubleValue());
                break;
            case "new":
                value = newObject(((String) valueInfo.get("type")));
                break;
            case "invoke":
                value = resolveInvokeExpr(valueInfo, body, localGenerator);
                break;
            default:
                value = resolveRef(valueInfo, body);
                break;
        }
        return value;
    }
    public static Value newObject(String objectType){
        Value value;
        if ("java.lang.String".equals(objectType)) {
            value = StringConstant.v((""));
        }
        else{
            RefType refType = (RefType) getType(objectType);
            if(refType==null){
                return null;
            }
            value = Jimple.v().newNewExpr(refType);
        }

        if (value==null){
            RefType refType = Scene.v().getRefType("java.lang.Object");
            value = Jimple.v().newNewExpr(refType);
        }
        return value;
    }
    public static Local resolveLocal(JSONObject refInfo, Body body, LocalGenerator localGenerator){
        Local local;
        int index = ((Long) refInfo.get("index")).intValue();

        if(index >= body.getLocalCount()) {
            String typeStr = (String) refInfo.get("type");
            Type localType;
            if (typeStr.equals("this")){
                localType = body.getMethod().getDeclaringClass().getType();
            }
            else if (typeStr.equals("None")){
                localType = NullConstant.v().getType();
            }
            else{
                localType = Scene.v().getType(typeStr);
            }
            local = localGenerator.generateLocal(localType);
        }
        else {
            local = getLocal(body, index);
        }

        return local;
    }
    public static Local resolveLeftLocal(JSONObject refInfo, Body body, LocalGenerator localGenerator){
        Local local;
        String typeStr = (String) refInfo.get("type");
        Type localType;
        if (typeStr.equals("this")){
            localType = body.getMethod().getDeclaringClass().getType();
        }
        else{
            localType = getType(typeStr);
        }
        local = localGenerator.generateLocal(localType);
        allocatedLocals.add(local);
        return local;
    }
    public static Local getLocal(Body body, int index){
        int i = 0;
        for (Local local : allocatedLocals) {
            if(i == index) {
                return local;
            }
            i++;
        }
        return null;
    }
    public static SootMethod makeMethodBySignature(String signature){
        // <DummyNative: void printf(None,'java.lang.String')>
        String subSignature = Scene.signatureToSubsignature(signature);
        String[] splitStr = subSignature.split(" ");

        String name = splitStr[1].split("\\(")[0];

        List<Type> parameterTypes = new LinkedList<>();

        String patternStr = "(?<=\\().*?(?=\\s*\\)[^)]*$)";
        Pattern pattern = Pattern.compile(patternStr);
        Matcher matcher = pattern.matcher(splitStr[1]);

        if(matcher.find()) {
            String paramStr = matcher.group();
            for(String param: paramStr.split(",")) {
                if(param.equals(dummyNativeClassName)){
                    parameterTypes.add(IntType.v());
                }
                else if(param.equals("")){
                    continue;
                }
                else {
                    parameterTypes.add(getType(param));
                }
            }
        }

        Type returnType = getType(splitStr[0]);

        return Scene.v().makeSootMethod(name, parameterTypes, returnType);
    }

    public static Type getType(String typeStr){
        Type type;
        type = Scene.v().getTypeUnsafe(typeStr);

        if(type==null){
            SootClass sootClass = Scene.v().getSootClass(typeStr);
            type = sootClass.getType();
        }

        return type;
    }

    public static Ref resolveRef(JSONObject refInfo, Body body){
        String stmtType = (String) refInfo.get("stmt_type");
        Ref ref;
        switch(stmtType){
            case "this_ref":
                ref = Jimple.v().newThisRef(body.getMethod().getDeclaringClass().getType());
                break;
            case "param_ref":
                int index = ((Long) refInfo.get("index")).intValue();
                Type paramType = getType((String) refInfo.get("type"));
                ref = Jimple.v().newParameterRef(paramType, index);
                break;
            case "field_ref":
                String className = (String) refInfo.get("class");
                String fieldName = (String) refInfo.get("name");
                Type fieldType = getType((String) refInfo.get("type"));
                boolean is_static = refInfo.get("is_static").equals("true");
                SootFieldRef sootFieldRef = Scene.v().makeFieldRef(Scene.v().getSootClass(className), fieldName, fieldType, is_static);
                if(is_static){
                    ref = Jimple.v().newStaticFieldRef(sootFieldRef);
                }
                else{
                    int baseIndex = ((Long) refInfo.get("base")).intValue();
                    Local base = getLocal(body, baseIndex);
                    ref = Jimple.v().newInstanceFieldRef(base, sootFieldRef);
                }
                // Todo: Jimple.v().newInstanceFieldRef()
                break;
            default:
                ref = null;
        }

        return ref;
    }
    public static void appendSourcesAndSinks(JSONArray sourceSignatures,String sourceSinkPath){
        boolean haveToExit = false;
        String[] sigArray;
        if(sourceSignatures != null) {
            sigArray = new String[sourceSignatures.size()];
            int i = 0;
            for (Object signature : sourceSignatures) {
                String sig = (String) signature;
                sigArray[i] = sig;
                String source = sig + " -> _SOURCE_";

                if (isExistsInFile(sourceSinkPath, source)) {
                    continue;
                }

                try {
                    Files.write(Paths.get(sourceSinkPath), ("\n" + source).getBytes(), StandardOpenOption.APPEND);
                    haveToExit = true;
                } catch (IOException e) {
                    //exception handling left as an exercise for the reader
                }
            }
        }
        else{
            sigArray = null;
        }
        for (SootMethod method : dummyNativeClass.getMethods()){
            String sig = method.getSignature();

            if(sigArray != null) {
                if (Arrays.asList(sigArray).contains(sig)) {
                    continue;
                }
            }
            String sink = sig + " -> _SINK_";
            // Todo: Check sink in text file

            if(isExistsInFile(sourceSinkPath, sink)){
                continue;
            }

            try {
                Files.write(Paths.get(sourceSinkPath), ("\n" + sink).getBytes(), StandardOpenOption.APPEND);
                haveToExit = true;
            }catch (IOException e) {
                //exception handling left as an exercise for the reader
            }
        }/*
        if(haveToExit){
            System.exit(777);
        }*/
    }
    public static boolean isExistsInFile(String sourceSinkPath, String sink){
        try (Stream<String> stream = Files.lines(Paths.get(sourceSinkPath))) {
            Optional<String> lineHavingTarget = stream.filter(l -> l.contains(sink)).findFirst();
            if(lineHavingTarget.isPresent()){
                return true;
            }
            // do whatever
        } catch (IOException e) {
            // log exception
        }
        return false;
    }
    public static List<Edge> parseEdges(JSONArray edges) {
        if(edges == null){
            return null;
        }

        List<Edge> edgeList = new LinkedList<>();
        for (Object edgeInfo : edges) {
            Edge edge = parseEdgeInfo((JSONObject) edgeInfo);
            if(edge != null)
                edgeList.add(edge);
        }

        return edgeList;
    }
    public static Edge parseEdgeInfo(JSONObject jsonObject){
        String srcSig = (String) jsonObject.get("src");
        String tgtSig = (String) jsonObject.get("tgt");
        String kindStr = (String) jsonObject.get("kind");
        long invokeIdx = (long) jsonObject.get("invoke_idx");

        SootMethod srcMethod = null;
        SootMethod tgtMethod = null;
        Stmt stmt = null;
        Kind kind = null;

        try{
            srcMethod = getSootMethod(srcSig);
            tgtMethod = getSootMethod(tgtSig);

            boolean isCallback = isServiceCallback(tgtMethod);
            if(isCallback){
                invokeIdx++;
            }

            stmt = getStmt(srcMethod, invokeIdx);
            // Retry
            if(stmt == null && isCallback){
                stmt = getStmt(srcMethod, invokeIdx);
            }

            kind = getKind(kindStr);
        } catch (RuntimeException e) {
            // Watch class when occurred exception
            SootClass sc = Scene.v().getSootClass((String) jsonObject.get("cls"));
            return null;
        }

        return new Edge(srcMethod, stmt, tgtMethod, kind);
    }

    public static SootMethod getSootMethod(String methodSig){
        return Scene.v().getMethod(methodSig);
    }

    public static Stmt getStmt(SootMethod sootMethod, long invokeIdx) {
        Body body = sootMethod.getActiveBody();
        if (body == null)
            return null;
        UnitPatchingChain units = body.getUnits();
        return traverseStmt(units, invokeIdx);
    }

    public static boolean isServiceCallback(SootMethod sootMethod){
        switch(sootMethod.getName()){
            case("onPreExecute"):
            case("doInBackground"):
            case("onProgressUpdate"):
            case("onCancelled"):
            case("onPostExecute"):
                return true;
            default:
                return false;
        }

        // Todo: return and param type check
    }

    public static Stmt traverseStmt(UnitPatchingChain units, long invokeIdx){
        int idx = 0;
        Stmt stmt = null;
        Stmt temp;

        for (Unit unit : units) {
            temp = (Stmt) unit;

            if(hasInvokeExpr(temp))
                idx++;

            if (idx == invokeIdx) {
                stmt = temp;
                break;
            }
        }

        return stmt;
    }

    public static boolean hasInvokeExpr(Stmt stmt){
        if(stmt instanceof AssignStmt){
            return ((AssignStmt) stmt).getRightOp() instanceof InvokeExpr;
        }
        else return stmt instanceof InvokeStmt;
    }

    public static Kind getKind(String kindStr) {
        switch (kindStr) {
            case "CLINIT":
                return Kind.CLINIT;
            case "VIRTUAL":
                return Kind.VIRTUAL;
            case "SPECIAL":
                return Kind.SPECIAL;
            case "INTERFACE":
                return Kind.INTERFACE;
            case "STATIC":
                return Kind.STATIC;
            default:
                return null;
        }
    }

}
