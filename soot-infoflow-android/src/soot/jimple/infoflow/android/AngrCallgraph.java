package soot.jimple.infoflow.android;

import org.json.simple.JSONArray;
import org.json.simple.JSONObject;
import org.json.simple.parser.JSONParser;
import org.json.simple.parser.ParseException;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import soot.*;
import soot.LocalGenerator;
import soot.jimple.*;
import soot.jimple.infoflow.android.iccta.IccLink;
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
    private static final Logger logger = LoggerFactory.getLogger(AngrCallgraph.class);
    private static boolean hasLoaded = false;
    static String dummyNativeClassName = "DummyNative";
    static SootClass dummyNativeClass;
    static List<Local> allocatedLocals;
    static Local dummyLocal;
    static int dummyIndex=0;
    static CallGraph cg;
    static Queue<Edge> edgeQueue = new LinkedList<>();
    static List<IccLink> iccLinks = new ArrayList<>();
    static JSONArray nodesJson = null;
    static JSONArray edgesJson = null;
    static JSONArray nativeSourcesJson = null;
    static JSONArray iccLinksJson = null;

    public static List<IccLink> getIccLinks(){
        return iccLinks;
    }

    public static boolean loadJson(InfoflowAndroidConfiguration config) {
        if (hasLoaded)
            return true;

        String jsonPath = config.getAnalysisFileConfig().getAngrJsonFile();
        String sourceSinkPath = config.getAnalysisFileConfig().getSourceSinkFile();

        byte[] jsonBytes;
        try {
            assert jsonPath != null;
            jsonBytes = Files.readAllBytes(Paths.get(jsonPath));
        } catch (IOException ioe) {
            ioe.printStackTrace();
            return false;
        }

        String jsonStr = new String(jsonBytes);
        JSONParser jp = new JSONParser();
        try {
            JSONObject jo = (JSONObject) jp.parse(jsonStr);
            nodesJson = (JSONArray) jo.get("nodes");
            edgesJson = (JSONArray) jo.get("edges");
            nativeSourcesJson = (JSONArray) jo.get("native_sources");
            iccLinksJson = (JSONArray) jo.get("icc_links");
        } catch (ParseException ignored) {
            return false;
        }
        logger.info("Done to load json file for DryJIN");
        logger.info("loadNodes");
        loadNodes();
        logger.info("loadEdges");
        loadEdges();
        logger.info("loadNativeSources");
        loadNativeSources(config.getAnalysisFileConfig().getSourceSinkFile());
        logger.info("loadIccLinks");
        loadIccLinks();
        hasLoaded = true;
        return true;
    };

    public static boolean loadNodes(){
        if(nodesJson == null){
            logger.info("Failed to load nodes for DryJIN.");
            return false;
        }

        dummyNativeClass = Scene.v().getSootClassUnsafe(dummyNativeClassName);
        dummyNativeClass.setModifiers(9);
        dummyNativeClass.setApplicationClass();

        for (Object node : nodesJson) {
            JSONObject jo = (JSONObject) node;
            // get method from class with params and ret
            SootMethod sootMethod = getMethod(jo);

            if(sootMethod==null || sootMethod.hasActiveBody()){
                continue;
            }

            sootMethod.setModifiers(Modifier.PUBLIC);       // To avoid concrete

            // load body
            allocatedLocals = new LinkedList<>();
            JimpleBody body = Jimple.v().newBody();
            body.setMethod(sootMethod);
            loadBody(jo, body, sootMethod);

            sootMethod.setActiveBody(body);
            if(sootMethod.getDeclaringClass().getName().equals("android.app.NativeActivity")) {
                insertInvokeNativeActivity(sootMethod);
            }
        }
        return true;
    }

    public static boolean loadEdges() {
        if(edgesJson == null){
            logger.error("Failed to load edges for DryJIN.");
            return false;
        }

        for (Object edgeInfo : edgesJson) {
            Edge edge = parseEdgeInfo((JSONObject) edgeInfo);
            if(edge != null)
                edgeQueue.add(edge);
        }
        return true;
    }

    public static boolean loadNativeSources(String sourceSinkPath) {
        if (dummyNativeClass != null && nativeSourcesJson != null) {
            appendSourcesAndSinks(nativeSourcesJson, sourceSinkPath);
            return true;
        }
        else {
            return false;
        }
    }

    public static boolean loadIccLinks() {
        if(iccLinksJson == null){
            logger.info("Failed to load nodes for DryJIN.");
            return false;
        }

        for (Object node : iccLinksJson) {
            JSONObject jo = (JSONObject) node;
            // get method from class with params and ret
            Long fromUIdx = (Long) jo.get("fromU");
            String fromSmSignature = (String) jo.get("fromSm");
            String destinationCSignature = (String) jo.get("destinationC");

            SootMethod fromSM = Scene.v().grabMethod(fromSmSignature);
            SootClass destinationC = Scene.v().getSootClassUnsafe(destinationCSignature);
            Unit fromU = null;
            int idx = 0;
            Body body = fromSM.getActiveBody();
            if (body != null) {
                UnitPatchingChain units = fromSM.getActiveBody().getUnits();

                for (Unit unit : fromSM.getActiveBody().getUnits()) {
                    if (idx == fromUIdx) {
                        fromU = unit;
                        break;
                    }
                    idx++;
                }

                IccLink iccLink = new IccLink(fromSM, fromU, destinationC);
                iccLink.setExit_kind("Activity");

                iccLinks.add(iccLink);
            }
        }
        return true;
    }

    public static void addEdges(CallGraph cg) {
        for (Edge edge : edgeQueue){
            cg.addEdge(edge);
        }
        edgeQueue.clear();
        edgesJson.clear();
    }

    public static void insertInvokeNativeActivity(SootMethod callbackMethod) {
        /*
        Leave it if we need later.
         */
        SootMethod dummyMethod = Scene.v().getMethod("<dummyMainClass: void dummyMainMethod(java.lang.String[])>");
//        SootMethod initMethod = Scene.v().getMethod("<android.app.NativeActivity: void init()>");

        Body activeBody = dummyMethod.getActiveBody();
        LocalGenerator localGenerator = Scene.v().createLocalGenerator(activeBody);
        UnitPatchingChain units = activeBody.getUnits();
        Unit lastStmt = units.getLast();
        units.removeLast();

        LinkedList<Value> emptyArgs = new LinkedList<>();
        Local newActivity = localGenerator.generateLocal(callbackMethod.getDeclaringClass().getType());
        NewExpr newExpr = Jimple.v().newNewExpr(callbackMethod.getDeclaringClass().getType());
        AssignStmt assignStmt = Jimple.v().newAssignStmt(newActivity, newExpr);
        units.add(assignStmt);

//        InvokeExpr invokeInitExpr = Jimple.v().newSpecialInvokeExpr(newActivity, initMethod.makeRef(), emptyArgs);
//        InvokeStmt invokeInitStmt = Jimple.v().newInvokeStmt(invokeInitExpr);
//        units.add(invokeInitStmt);

        InvokeExpr invokeExpr = Jimple.v().newVirtualInvokeExpr(newActivity, callbackMethod.makeRef(), emptyArgs);
        InvokeStmt invokeStmt = Jimple.v().newInvokeStmt(invokeExpr);
        units.add(invokeStmt);

        units.add(lastStmt);

        addEdgeForInvoke(invokeStmt, dummyMethod, callbackMethod, Kind.VIRTUAL);
    }
    public static SootMethod getMethod(JSONObject jo){
        String className = (String) jo.get("class");
        String methodName = (String) jo.get("name");
        String ret = (String) jo.get("ret");
        String params = (String) jo.get("params");
        String subSig = ret + " " + methodName + params;
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
        else if(sootMethod==null && sootClass.getName().equals("android.app.NativeActivity")){
            List<Type> paramTypes = new LinkedList<Type>();
            Type retType = Scene.v().getType(ret);

            for(String param: params.replace("(", "").replace(")", "").split(",")){
                paramTypes.add(Scene.v().getType(param));
            }

            sootMethod = Scene.v().makeSootMethod(methodName, paramTypes, retType);
            sootMethod.setModifiers(Modifier.PUBLIC + Modifier.STATIC);
            sootClass.addMethod(sootMethod);
        }
        return sootMethod;
    }
    public static void loadBody(JSONObject jo, JimpleBody body, SootMethod sootMethod){
        LocalGenerator lg = Scene.v().createLocalGenerator(body);
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
                    Kind kind;
                    if(tgt.isStatic()){
                        kind = Kind.STATIC;
                    }else{
                        kind = Kind.VIRTUAL;
                    }
                    addEdgeForInvoke(stmt, src, tgt, kind);
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
        edgeQueue.add(edge);
    }

    public static InvokeExpr resolveInvokeExpr(JSONObject exprInfo, Body body, LocalGenerator localGenerator) {
        String signature = (String) exprInfo.get("callee");
        SootMethod calleeMethod = Scene.v().grabMethod(signature);

        if (calleeMethod == null) {
            calleeMethod = makeMethodBySignature(signature);
            if ((Boolean) exprInfo.get("is_static")) {
                calleeMethod.setModifiers(Modifier.PUBLIC + Modifier.STATIC);
            }
            else{
                calleeMethod.setModifiers(Modifier.PUBLIC);
            }
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

        if (!(Boolean) exprInfo.get("is_static")) {
            Local base = getLocal(body, ((Long) exprInfo.get("base")).intValue());
            expr = Jimple.v().newVirtualInvokeExpr(base, ref, args);
        }
        else {
            expr = Jimple.v().newStaticInvokeExpr(calleeMethod.makeRef(), args);
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
            if (objectType.contains("[]")) {
                ArrayType refType = (ArrayType) getType(objectType);
                if(refType==null){
                    return null;
                }
                Value size = IntConstant.v(16);
                value = Jimple.v().newNewArrayExpr(refType, size);
            }
            else {
                RefType refType = (RefType) getType(objectType);
                if(refType==null){
                    return null;
                }
                value = Jimple.v().newNewExpr(refType);
            }
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
                if(index == -1) {
                    index=dummyIndex+1;
                }
                dummyIndex=index;
                Type paramType = getType((String) refInfo.get("type"));
                ref = Jimple.v().newParameterRef(paramType, index);
                break;
            case "field_ref":
                String className = (String) refInfo.get("class");
                String fieldName = (String) refInfo.get("name");
                Type fieldType = getType((String) refInfo.get("type"));
                boolean is_static = (boolean) refInfo.get("is_static");
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
        }
//        System.exit(777);
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