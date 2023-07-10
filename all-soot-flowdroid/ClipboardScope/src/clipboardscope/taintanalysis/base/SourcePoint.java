package clipboardscope.taintanalysis.base;

import java.util.HashSet;

import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.toolkits.graph.Block;

public class SourcePoint {
	SootMethod methodLocation;
	Block blockLocation;
	Unit instructionLocation;
	Value tartgetValue;
	HashSet<String> targetField;

	public SourcePoint(SootMethod methodLocation, Block blockLocation, Unit instructionLocation, Value tartgetValue, HashSet<String> sField) {
		this.methodLocation = methodLocation;
		this.blockLocation = blockLocation;
		this.instructionLocation = instructionLocation;
		this.tartgetValue = tartgetValue;
		this.targetField = sField;
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
	}

	public Unit getInstructionLocation() {
		return instructionLocation;
	}

	public void setInstructionLocation(Unit instructionLocation) {
		this.instructionLocation = instructionLocation;
	}

	public Value getTartgetValue() {
		return tartgetValue;
	}
	
	public HashSet<String> getTartgetField() {
		return targetField;
	}

	public void setTartgetValue(Value tartgetValue) {
		this.tartgetValue = tartgetValue;
	}

}
