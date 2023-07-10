package clipboardscope.taintanalysis.solver;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import clipboardscope.taintanalysis.utility.ListUtility;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.DefinitionStmt;
import soot.jimple.InvokeExpr;
import soot.toolkits.graph.Block;

public class CallStackItem {
	SootMethod smethd;
	Block blcok;
	Unit currentInstruction;
	Value returnTarget;
	boolean isFirstInterf;
	String interfName;
	HashMap<Value, HashSet<String>> interestedPrefToAdd;
	ArrayList<Value> param2Var;
	InvokeExpr invokExpr;
	ArrayList<DefinitionStmt> cashedDefStmt;

	@SuppressWarnings("unchecked")
	public CallStackItem(SootMethod smethd, Block blcok, Unit currentInstruction, Value returnTarget, String interfName,
			boolean isFirstIntef, HashMap<Value, HashSet<String>> interestedPref, InvokeExpr invokExpr, 
			ArrayList<Value> param2Var, ArrayList<DefinitionStmt> cashedDefStmt) {
		super();
		this.smethd = smethd;
		this.blcok = blcok;
		this.currentInstruction = currentInstruction;
		this.returnTarget = returnTarget;
		this.interfName = interfName;
		this.isFirstInterf = isFirstIntef;
		this.interestedPrefToAdd = new HashMap<>();
		this.interestedPrefToAdd.putAll(interestedPref);
		this.param2Var = (ArrayList<Value>) param2Var.clone();
		this.invokExpr = invokExpr;
		this.cashedDefStmt = (ArrayList<DefinitionStmt>) cashedDefStmt.clone();
	}

	public SootMethod getSmethd() {
		return smethd;
	}

	public void setSmethd(SootMethod smethd) {
		this.smethd = smethd;
	}

	public Block getBlcok() {
		return blcok;
	}

	public void setBlcok(Block blcok) {
		this.blcok = blcok;
	}

	public Unit getCurrentInstruction() {
		return currentInstruction;
	}

	public void setCurrentInstruction(Unit currentInstruction) {
		this.currentInstruction = currentInstruction;
	}

	public Value getReturnTarget() {
		return returnTarget;
	}

	public void setReturnTarget(Value returnTarget) {
		this.returnTarget = returnTarget;
	}
	
	public String getInterfName() {
		return this.interfName;
	}
	
	public boolean isFirstInterf() {
		return this.isFirstInterf;
	}
	
	public HashMap<Value, HashSet<String>> getInterestedPref() {
		return this.interestedPrefToAdd;
	}
	
	public InvokeExpr getInvokeExpr() {
		return this.invokExpr;
	}
	
	@SuppressWarnings("unchecked")
	public void setParamReachableSet(ArrayList<Value> paramReachableSet) {
		this.param2Var = (ArrayList<Value>) paramReachableSet.clone();
	}
	
	public ArrayList<Value> getParam2Var() {
		return this.param2Var;
	}
	
	public ArrayList<DefinitionStmt> getCashedDefStmt() {
		return this.cashedDefStmt;
	}
}
