package clipboardscope.taintanalysis.solver;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Stack;
import java.util.concurrent.TimeUnit;

import clipboardscope.main.runTest;
import clipboardscope.taintanalysis.base.SourcePoint;
import clipboardscope.taintanalysis.base.TaintQuestion;
import clipboardscope.taintanalysis.main.QuestionGenerator;
import clipboardscope.taintanalysis.utility.BlockGenerator;
import clipboardscope.taintanalysis.utility.ListUtility;
import clipboardscope.taintanalysis.utility.Logger;
import clipboardscope.taintanalysis.utility.TimeUtility;
import soot.Body;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.InvokeExpr;
import soot.jimple.StaticFieldRef;
import soot.jimple.ThisRef;
import soot.toolkits.graph.Block;

public class TaintQuestionSolver {
	public static HashSet<String> staticFieldVariableSet;
	public static HashSet<String> newStaticFieldSet;
//	public static InterfaceTree tree = null;
	public static int processedInstruction = 0;
	
	public ArrayList<TaintQuestion> solve(TaintQuestion originTq) {
		staticFieldVariableSet = new HashSet<String>();
		newStaticFieldSet = new HashSet<String>();
		
		ArrayList<TaintQuestion> tqList = new ArrayList<TaintQuestion>();
		
		int iterTimes = 0;
		runTest.questionTimeout = false;
		Thread thread = TimeUtility.startWatcherOneQuestionBruce(3 * 60);
		tqList.addAll(solveOneTq(originTq, originTq.getSourcep()));
		while (newStaticFieldSet.size() > 0 && !runTest.questionTimeout && !runTest.timeout) {
			iterTimes++;
			if (iterTimes >= 2) {
//				System.out.println("Shut down this question since exceeding iteration time limit");
				break;
			}
			staticFieldVariableSet.addAll(newStaticFieldSet);
			HashSet<String> tempNewSet = (HashSet<String>) newStaticFieldSet.clone();
			newStaticFieldSet = new HashSet<String>();
			
			for (SootClass sclas : Scene.v().getClasses()) {
				String scName = sclas.toString();
				for (SootMethod smthd : ListUtility.clone(sclas.getMethods())) {
					if (!smthd.isConcrete()) continue;
	
					Body body = smthd.retrieveActiveBody();
					if (body == null) continue;
					List<Block> bs = BlockGenerator.getInstance().generate(body).getBlocks();
					for (Block block : bs) {
						for (Unit unit : block) {
							if (unit instanceof AssignStmt) {
								Value rop = ((AssignStmt) unit).getRightOp();
								if (rop instanceof StaticFieldRef && tempNewSet.contains(((StaticFieldRef)rop).getField().toString())) {
									QuestionGenerator qg = new QuestionGenerator();
									TaintQuestion curTq = qg.generateOneStaticFieldQuestion(smthd, block, unit, ((AssignStmt) unit).getLeftOp(), false, originTq);
//									System.out.println("Found one source: " + unit.toString() + " in " + smthd.toString());
									tqList.addAll(solveOneTq(curTq, originTq.getSourcep()));
								}
							}
						}
					}
				}
			}
			
		}
		if (thread.isAlive())
			thread.interrupt();
		return tqList;
	}
	
	public ArrayList<TaintQuestion> solveOneTq(TaintQuestion tq, SourcePoint originSp){
		processedInstruction = 0;
		ArrayList<TaintQuestion> tqList = new ArrayList<TaintQuestion>();
		
		SimulationContext target = null;
		while (!runTest.questionTimeout && !runTest.timeout) {
			// printState(tq);

			while (tq.getsContexts().size() > 100000){
//				System.out.println("*******Out of size remove current Context");
				tq.getsContexts().remove(tq.getsContexts().size() - 1);
			}
			
			target = null;
			for (SimulationContext sContext : tq.getsContexts()) {
				if (!sContext.isTerminated()) {
					target = sContext;
					break;
				}
			}

			if (target == null) {
				break;
			}

			processOneInstruction(tq, target);
		}
		
		tqList.add(tq);
		print(tq);
		
		return tqList;
	}

	public void processOneInstruction(TaintQuestion tq, SimulationContext sContext) {

		List<SimulationContext> diversed = SimulationEngine.getInstance().oneStepForward(tq, sContext);

		for (SimulationContext sc : diversed) {
			tq.addSContexts(sc);
		}
	}

	public void print(TaintQuestion tq) {
		for (SimulationContext sContext : tq.getsContexts()) {
			Logger.print(sContext.isContainsSink() + " " + sContext.hashCode());
			for (StmtItem u : sContext.getInstructionTrace()) {
				Logger.print("    " + u.isContainsSink() + " " + u.getU());
				Logger.print("        " + u.getUnitIndex() + " " + u.getSm());
			}
		}
	}
	
	public static HashSet<String> getFieldsInChildClass(String sField) {

		HashSet<String> fieldSet = new HashSet<>();
		fieldSet.add(sField);
//		String className = sField.substring(1, sField.indexOf(":"));
//		if (!runTest.childrenTable.containsKey(Scene.v().getSootClass(className))) 
//			return fieldSet;
//		
//		HashSet<SootClass> toDoSet = new HashSet<SootClass>();
//		
//		
//		String FieldName = sField.substring(sField.indexOf(":"), sField.length());
//		
//		toDoSet.addAll(runTest.childrenTable.get(Scene.v().getSootClass(className)));
//		
//		while (!toDoSet.isEmpty()) {
//			SootClass childClass = toDoSet.iterator().next();
//			toDoSet.remove(childClass);
//			fieldSet.add("<" + childClass.getName() + FieldName);
//		}
		return fieldSet;
	}

	private void printState(TaintQuestion tq) {

		int ended = 0;
		int all = 0;
		for (SimulationContext sContext : tq.getsContexts()) {

			if (sContext.isTerminated())
				ended++;
			all++;

		}

		System.out.println(all + " / " + ended);
	}
}
