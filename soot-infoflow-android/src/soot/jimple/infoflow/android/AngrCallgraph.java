package soot.jimple.infoflow.android;

import org.json.simple.JSONArray;
import org.json.simple.JSONObject;
import org.json.simple.parser.JSONParser;
import org.json.simple.parser.ParseException;
import soot.*;
import soot.jimple.AssignStmt;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.Stmt;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.LinkedList;
import java.util.List;

public class AngrCallgraph {

    public static CallGraph newCallgraph(){
        //CallGraph cg = new CallGraph();
        CallGraph cg = Scene.v().getCallGraph();
        List<Edge> edges = getEdges();
        assert edges != null;

        for(Edge edge: edges) {
            cg.addEdge(edge);
        }

        return cg;
    }
    public static List<Edge> getEdges(){
        byte[] bytes;
        try {
            bytes = Files.readAllBytes(Paths.get("C:\\Users\\msec\\AndroidStudioProjects\\ActivityCommunication31\\app\\build\\outputs\\apk\\debug\\callgraph.json"));
        } catch (IOException ioe){
            ioe.printStackTrace();
            return null;
        }

        String str = new String(bytes);
        return parse(str);
    }
    public static List<Edge> parse(String jsonStr) {
        boolean b = true;
        JSONParser jp = new JSONParser();
        JSONArray ja = null;

        try {
            ja = (JSONArray) jp.parse(jsonStr);
        } catch (ParseException ignored){
        }

        if(ja == null){
            return null;
        }

        List<Edge> edgeList = new LinkedList<>();
        for (Object edgeInfo : ja) {
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

    public static Stmt getStmt(SootMethod method, long invokeIdx) {
        Body body = method.getActiveBody();
        UnitPatchingChain units = body.getUnits();
        return traverseStmt(units, invokeIdx);
    }

    public static boolean isServiceCallback(SootMethod method){
        switch(method.getName()){
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
