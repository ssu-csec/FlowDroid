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

import java.io.*;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.util.*;
import java.util.stream.Stream;

public class AngrCallgraph {
    static String dummyClassName = "nativemethod";
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
        try {
            JSONObject jo = (JSONObject) jp.parse(jsonStr);
            nodesJson = (JSONArray) jo.get("nodes");
            edgesJson = (JSONArray) jo.get("edges");
        } catch(ParseException ignored){
        }

        cg = Scene.v().getCallGraph();
        if (nodesJson != null) {
            loadDummyNodes(nodesJson, sourceSinkPath);
        }
        //CallGraph cg = new CallGraph();
        List<Edge> edges = parseEdges(edgesJson);
        assert edges != null;

        for (Edge edge : edges) {
            cg.addEdge(edge);
        }

        return cg;
    }
    public static void loadDummyNodes(JSONArray nodes, String sourceSinkPath){
        if(nodes == null){
            return;
        }

        SootClass nativeClass = Scene.v().getSootClassUnsafe(dummyClassName);
        nativeClass.setModifiers(9);
        nativeClass.setApplicationClass();

        for (Object edgeInfo : nodes) {
            JSONObject jo = (JSONObject) edgeInfo;
            // get method from class with params and ret
            SootMethod sootMethod = getMethod(jo);

            // load body
            JimpleBody body = Jimple.v().newBody();
            sootMethod.setModifiers(Modifier.PUBLIC);       // To avoid concrete
            body.setMethod(sootMethod);

            loadBody(jo, body, sootMethod, nativeClass);
            sootMethod.setActiveBody(body);
            appendSinks(nativeClass, sourceSinkPath);
        }
    }
    public static SootMethod getMethod(JSONObject jo){
        String className = (String) jo.get("class");
        String methodName = (String) jo.get("name");
        String retType = (String) jo.get("ret");
        String params = (String) jo.get("params");
        String subSig = retType + " " + methodName + params;

        SootClass sootClass = Scene.v().getSootClassUnsafe(className);
        return sootClass.getMethod(subSig);
    }
    public static void loadBody(JSONObject jo, JimpleBody body, SootMethod sootMethod, SootClass nativeClass){
        LocalGenerator lg = new LocalGenerator(body);
        List<JSONObject> stmtList = (List<JSONObject>) jo.get("body");
        List<Local> localList = new LinkedList<Local>();

        Local thisLocal = lg.generateLocal(sootMethod.getDeclaringClass().getType());
        body.getUnits().add(Jimple.v().newIdentityStmt(thisLocal, Jimple.v().newThisRef(sootMethod.getDeclaringClass().getType())));
        for (JSONObject stmt : stmtList){
            String stmtType = (String) stmt.get("type");
            if(stmtType.equals("assign")){
                int local = Long.valueOf((long) stmt.get("local")).intValue();

                Type paramType = sootMethod.getParameterType(local);
                Local paramLocal = lg.generateLocal(paramType);
                ParameterRef paramRef = Jimple.v().newParameterRef(paramType, local);
                localList.add(paramLocal);
                body.getUnits().add(Jimple.v().newIdentityStmt(paramLocal, paramRef));

            }
            else if(stmtType.equals("invoke")){
                final InvokeExpr invokeExpr;
                String callee = (String) stmt.get("callee");
                List<Long> argsInfo = (List<Long>) stmt.get("args");
                List<Value> args = new LinkedList<Value>();
                List<Type> argTypes = new LinkedList<Type>();
                for (long argLong : argsInfo) {
                    int argInt = Long.valueOf(argLong).intValue();
                    Local paramLocal = localList.get(argInt);
                    argTypes.add(paramLocal.getType());
                    args.add(paramLocal);
                }

                SootMethod calleeMethod = nativeClass.getMethodByNameUnsafe(callee);
                if (calleeMethod == null) {
                    calleeMethod = Scene.v().makeSootMethod(callee, argTypes, VoidType.v());
                    calleeMethod.setModifiers(Modifier.PUBLIC + Modifier.STATIC);
                    calleeMethod.setPhantom(true);
                    nativeClass.addMethod(calleeMethod);
                }

                invokeExpr = Jimple.v().newStaticInvokeExpr(calleeMethod.makeRef(), args);
                Stmt statement;
                statement = Jimple.v().newInvokeStmt(invokeExpr);
                body.getUnits().add(statement);

                Edge edge = new Edge(sootMethod, statement, calleeMethod, Kind.STATIC);
                cg.addEdge(edge);
            }
        }
        body.getUnits().add(Jimple.v().newReturnVoidStmt());
    }
    public static void appendSinks(SootClass nativeClass, String sourceSinkPath){
        boolean haveToExit = false;
        for (SootMethod method : nativeClass.getMethods()){
            String sig = method.getSignature();
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
            if(edge != null && !edge.tgt().getDeclaringClass().toString().startsWith("android."))
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
