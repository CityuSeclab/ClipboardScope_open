package clipboardscope.taintanalysis.solver;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import clipboardscope.main.runTest;
import clipboardscope.taintanalysis.utility.ListUtility;

import java.util.Set;
import java.util.Stack;

import soot.SootField;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.ArrayRef;
import soot.jimple.AssignStmt;
import soot.jimple.CastExpr;
import soot.jimple.DefinitionStmt;
import soot.jimple.FieldRef;
import soot.jimple.InstanceFieldRef;
import soot.toolkits.graph.Block;

public class SimulationContext {
	SootMethod methodLocation;
	Block blockLocation;
	Unit instructionLocation;

	HashMap<Value, HashSet<String>> intrestedVariable;	// If taint specific fields, list in the set
														// else if taint the whole variable, the set is empty 
														// (usually created because of exceeding the max depth)
//	HashSet<Value> intrestedVariable;
	HashSet<String> intrestedGlobalVariable;
	HashMap<Integer, HashSet<String>> taintedParams;	// the tainted parameters and the corresponding fields 
														// in the current function. -1 -- base; 0,1,2...--params 0, 1, 2
	ArrayList<Value> param2Var;
	ArrayList<DefinitionStmt> cashedAssgnStmt;
	
	int invokeLayer;	// The layer of invoke
	int maxAssignStmtCashSize = 10;
	
//	Bruce
	HashSet<Value> curInterestedVariable=null;
	

	ArrayList<Block> blockTrace;
	ArrayList<StmtItem> instructionTrace;
//	ArrayList<>
	
	Stack<CallStackItem> callStack;

	boolean terminated = false;

	boolean containsSink = false;
	
	boolean isInterestedInBase = false;

	@SuppressWarnings("unchecked")
	public SimulationContext(SimulationContext src) {
		this.methodLocation = src.getMethodLocation();
		this.blockLocation = src.getBlockLocation();
		this.instructionLocation = src.getInstructionLocation();
		this.intrestedVariable = (HashMap<Value, HashSet<String>>) src.getIntrestedVariable().clone();
		this.intrestedGlobalVariable = (HashSet<String>) src.getIntrestedGlobalVariable().clone();
		this.blockTrace = (ArrayList<Block>) src.getBlockTrace().clone();
		this.instructionTrace = (ArrayList<StmtItem>) src.getInstructionTrace().clone();
		this.callStack = (Stack<CallStackItem>) src.getCallStack().clone();
		this.invokeLayer = src.invokeLayer;
		this.containsSink = src.isContainsSink();
		this.taintedParams = (HashMap<Integer, HashSet<String>>) src.taintedParams.clone();
		this.param2Var =  (ArrayList<Value>) src.param2Var.clone();
		this.cashedAssgnStmt = (ArrayList<DefinitionStmt>) src.getCashedAssignStmt().clone();
		this.curInterestedVariable = (HashSet<Value>) src.getCurInterestedVariable().clone();
	}

	public SimulationContext(SootMethod methodLocation, Block blockLocation, Unit instructionLocation) {
		this.intrestedVariable = new HashMap<Value, HashSet<String>>();
		this.intrestedGlobalVariable = new HashSet<String>();
		this.instructionTrace = new ArrayList<StmtItem>();
		this.blockTrace = new ArrayList<Block>();
		this.callStack = new Stack<CallStackItem>();
		this.methodLocation = methodLocation;
		this.setBlockLocation(blockLocation);
		this.instructionLocation = instructionLocation;
		this.curInterestedVariable = new HashSet<>();
		add2InstructionTrace(methodLocation, blockLocation, instructionLocation, true);
		this.invokeLayer = 0;
		this.taintedParams = new HashMap<Integer, HashSet<String>>();
		this.param2Var = new ArrayList<Value>();
		this.resetCashedAssignStmt();
	}

	public SootMethod getMethodLocation() {
		return methodLocation;
	}

	public void setMethodLocation(SootMethod methodLocation) {
		this.methodLocation = methodLocation;
	}

	public Block getBlockLocation() {
		return blockLocation;
	}

	public void setBlockLocation(Block blockLocation) {
		this.blockLocation = blockLocation;
		blockTrace.add(blockLocation);
	}

	public Unit getInstructionLocation() {
		return instructionLocation;
	}

	public void setInstructionLocation(Unit instructionLocation, boolean containsInteresting) {
		this.instructionLocation = instructionLocation;
	}
//	public void setInstructionLocation(Unit instructionLocation, boolean containsInteresting, Value iv) {
//		this.instructionLocation = instructionLocation;
//		this.curInterestedVariable = iv;
//	}

	public boolean isTerminated() {
		return terminated || intrestedVariable.isEmpty();
	}

	public void setTerminated(boolean terminated) {
		this.terminated = terminated;
	}

	public HashSet<String> getIntrestedGlobalVariable() {
		return intrestedGlobalVariable;
	}
	
	public HashMap<Value, HashSet<String>> getIntrestedVariable() {
		return intrestedVariable;
	}
	
	public HashSet<Value> getIntrestedBaseVariable() {
		HashSet<Value> keySet = new HashSet<>();
		for (Value baseVar : getIntrestedVariable().keySet())
			keySet.add(baseVar);
		return keySet;
	}

	public void setIntrestedVariable(HashMap<Value, HashSet<String>> intrestedVariable) {
		this.intrestedVariable = (HashMap<Value, HashSet<String>>) intrestedVariable.clone();
	}

	public void addIntrestedVariable(Value baseVar, HashSet<String> sField) {
		HashSet<String> setToAdd = sField == null || sField.isEmpty() ? new HashSet<>() : (HashSet<String>) sField.clone();
		if (this.intrestedVariable.containsKey(baseVar)) setToAdd.addAll(this.intrestedVariable.get(baseVar));
		this.intrestedVariable.put(baseVar, setToAdd);
	}
	
	public void removeIntrestedVariable(Value baseVar, HashSet<String> sField) {
		if (sField == null || sField.isEmpty()) this.intrestedVariable.remove(baseVar);
		else if (this.isIntrested(baseVar)){
			HashSet<String> sf = this.intrestedVariable.get(baseVar);
			sf.removeAll(sField);
			if (sf.isEmpty()) this.intrestedVariable.remove(baseVar);
		}
	}
	
	public void addAllIntrestedVariable(HashMap<Value, HashSet<String>> intrestedVariables) {
		this.intrestedVariable.putAll(intrestedVariables);
	}

	public boolean isIntrested(Value r) {
		Value var = null;
		String field = null;
		if (r instanceof ArrayRef) var = ((ArrayRef) r).getBase();
		else if (r instanceof InstanceFieldRef) {
			var = ((InstanceFieldRef) r).getBase();
			field = ((InstanceFieldRef) r).getField().toString();
		}
		else if (r instanceof CastExpr) var = ((CastExpr) r).getOp();
		else var = r;
		if (getIntrestedVariable().containsKey(var))
			if (field != null) return this.intrestedVariable.get(var).contains(field) || this.intrestedVariable.get(var).isEmpty();
			else return true;
		return false;
	}
	
	public boolean containsIntrested(List<Value> intrs) {
		for (Value val : intrs)
			if (isIntrested(val))
				return true;

		return false;
	}

	public ArrayList<Block> getBlockTrace() {
		return blockTrace;
	}

	public void setBlockTrace(ArrayList<Block> blockTrace) {
		this.blockTrace = blockTrace;
	}

	public ArrayList<StmtItem> getInstructionTrace() {
		return instructionTrace;
	}

	public void setInstructionTrace(ArrayList<StmtItem> instructionTrace) {
		this.instructionTrace = instructionTrace;
	}

	public void add2InstructionTrace(SootMethod methodLocation, Block blockLocation, Unit instructionLocation, boolean containsInteresting) {
		StmtItem sItem = new StmtItem(methodLocation, blockLocation, instructionLocation);
		sItem.setContainsInteresting(containsInteresting);
		this.getInstructionTrace().add(sItem);
	}
	
	public void add2InstructionTraceSink(SootMethod methodLocation, Block blockLocation, Unit instructionLocation, boolean containsInteresting) {
		// Only for recording network getOutputStream
		StmtItem sItem = new StmtItem(methodLocation, blockLocation, instructionLocation);
		sItem.setContainsInteresting(containsInteresting);
		sItem.setContainsSink(true, new HashSet<>());
		this.getInstructionTrace().add(sItem);
	}

	public boolean isContainsSink() {
		return containsSink;
	}

//	public void setContainsSink(boolean containsSink) {
//		this.containsSink = containsSink;
//		this.getInstructionTrace().get(this.getInstructionTrace().size() - 1).setContainsSink(containsSink);
//	}
	
	public void setContainsSink(boolean containsSink, HashSet<Value> curIntst) {
		this.containsSink = containsSink;
//		this.getInstructionTrace().get(this.getInstructionTrace().size() - 1).setContainsSink(containsSink);
		this.getInstructionTrace().get(this.getInstructionTrace().size() - 1).setContainsSink(containsSink, curIntst);
	}

	public Stack<CallStackItem> getCallStack() {
		return callStack;
	}

	public void setCallStack(Stack<CallStackItem> callStack) {
		this.callStack = callStack;
	}
	
	public HashSet<Value> getCurInterestedVariable() {
		return curInterestedVariable;
	}

//	public void setCurInterestedVariable(Value curInterestedVariable) {
	public void addCurInterestedVariable(Value curInterestedVariable) {
		this.curInterestedVariable.add(curInterestedVariable);
	}
	
	public void resetCurInterestedVariable() {
		this.curInterestedVariable = new HashSet<>();
	}
	
	public HashMap<Integer, HashSet<String>> getTaintedParams() {
		return this.taintedParams;
	}
	
	public void setParam2Var(ArrayList<Value> param2Var) {
		this.param2Var = (ArrayList<Value>) param2Var.clone();
	}
	
	public ArrayList<Value> getParam2Var() {
		return this.param2Var;
	}
	
	public ArrayList<DefinitionStmt> getCashedAssignStmt() {
		return this.cashedAssgnStmt;
	}
	
	public void resetCashedAssignStmt() {
		this.cashedAssgnStmt = new ArrayList<>();
	}

	public void insertOneDefStmtToCash(DefinitionStmt s) {
		this.cashedAssgnStmt.add(s);
		if (this.cashedAssgnStmt.size() > maxAssignStmtCashSize) 
			this.cashedAssgnStmt.remove(0);
	}
	

	
}
