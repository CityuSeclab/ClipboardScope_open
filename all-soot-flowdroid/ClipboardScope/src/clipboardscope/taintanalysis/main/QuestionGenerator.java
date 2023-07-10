package clipboardscope.taintanalysis.main;

import java.io.File;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.List;
import java.util.Set;
import java.util.Map.Entry;

import clipboardscope.main.runTest;
import clipboardscope.stringvsa.utility.MethodUtility;
import clipboardscope.taintanalysis.base.SinkMethod;
import clipboardscope.taintanalysis.base.SourcePoint;
import clipboardscope.taintanalysis.base.TaintQuestion;
import clipboardscope.taintanalysis.solver.SimulationContext;
import clipboardscope.taintanalysis.solver.StmtItem;
import clipboardscope.taintanalysis.solver.TaintQuestionSolver;
import clipboardscope.taintanalysis.utility.BlockGenerator;
import clipboardscope.taintanalysis.utility.ListUtility;
import clipboardscope.taintanalysis.utility.Logger;
import soot.Body;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.baf.IfCmpEqInst;
import soot.coffi.class_element_value;
import soot.jimple.AssignStmt;
import soot.jimple.IdentityStmt;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InterfaceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.NewExpr;
import soot.jimple.ParameterRef;
import soot.jimple.StringConstant;
import soot.jimple.internal.JArrayRef;
import soot.options.LCMOptions;
import soot.tagkit.SourceLnNamePosTag;
import soot.toolkits.graph.Block;
import soot.util.Chain;

public class QuestionGenerator {
	ArrayList<TaintQuestion> tqInput;
	ArrayList<TaintQuestion> tqArray;

	List<TaintQuestion> solvedInput = new ArrayList<TaintQuestion>();
	List<TaintQuestion> solvedArray = new ArrayList<TaintQuestion>();
	
	
	public QuestionGenerator generateInputQuestions() {


		tqInput = new ArrayList<TaintQuestion>();
		tqArray = new ArrayList<TaintQuestion>();
		
		
		for (SootClass sclas : Scene.v().getClasses()) {
			String scName = sclas.toString();
			if (sclas.isApplicationClass() && sclas.hasSuperclass() && sclas.getSuperclass().isApplicationClass()){
				if (!runTest.childrenTable.containsKey(sclas.getSuperclass()))
					runTest.childrenTable.put(sclas.getSuperclass(), new HashSet<SootClass>());
				runTest.childrenTable.get(sclas.getSuperclass()).add(sclas);
				
			}
			
			for (SootMethod smthd : ListUtility.clone(sclas.getMethods())) {
				if (!smthd.isConcrete()) {	// For interface XX {} and abstract class, get their methods' templates
					if (sclas.isApplicationClass()){
						String interfName = smthd.getDeclaringClass().toString();
						String mthdName = clipboardscope.taintanalysis.utility.MethodUtility.getMthdTemplt(smthd);
						if (!runTest.interfMthdTplt.containsKey(interfName)) 
							runTest.interfMthdTplt.put(interfName, new HashSet<String>());
						runTest.interfMthdTplt.get(interfName).add(mthdName);
					}
					continue;
				}
				
				Body body = smthd.retrieveActiveBody();
				if (body == null)
					continue;
				List<Block> bs = BlockGenerator.getInstance().generate(body).getBlocks();
				for (Block block : bs) {
					for (Unit unit : block) {
						if (unit instanceof AssignStmt) {
							if (((AssignStmt) unit).getRightOp() instanceof InvokeExpr) {
								if (runTest.inputMetds.contains(((InvokeExpr) ((AssignStmt) unit).getRightOp()).getMethodRef().getSignature())){
									System.out.println("Found one source: " + unit.toString() + " in " + smthd.getSignature());
									generateOneQuestion(smthd, block, unit, ((AssignStmt) unit).getLeftOp(), null, true, null);	// interest in the left op
									
								}
							} 
						}

					}
				}
			}
		}

		
		for (SootClass sclas : Scene.v().getClasses()) {
			String scName = sclas.toString();
			String superClassName = null;
			if (sclas.hasSuperclass()) superClassName = sclas.getSuperclass().toString();
			for (SootMethod smthd : ListUtility.clone(sclas.getMethods())) {
				if (!smthd.isConcrete()) continue;
				
				String mthdName = clipboardscope.taintanalysis.utility.MethodUtility.getMthdTemplt(smthd);
				
				for (SootClass Interf : sclas.getInterfaces()) {
					String interfName = Interf.toString();

					if (runTest.interfMthdTplt.get(interfName) != null && runTest.interfMthdTplt.get(interfName).contains(mthdName)) {
						if (!runTest.i2c.containsKey(interfName)) 
							runTest.i2c.put(interfName, new ArrayList<SootMethod>());
						runTest.i2c.get(interfName).add(smthd);

					}
				}
				
				if (superClassName == null) continue;
				if (runTest.interfMthdTplt.get(superClassName) != null && runTest.interfMthdTplt.get(superClassName).contains(mthdName)) {
					if (!runTest.i2c.containsKey(superClassName)) 
						runTest.i2c.put(superClassName, new ArrayList<SootMethod>());
					runTest.i2c.get(superClassName).add(smthd);

				}
				
			}
			
		}
		
		return this;
	}

	private void generateOneQuestion(SootMethod smthd, Block block, Unit unit, Value value, HashSet<String> sField, boolean isInitial, TaintQuestion originTq) {
		HashMap<String, Integer> a = new HashMap<>();

		SourcePoint sp = new SourcePoint(smthd, block, unit, value, sField);

		TaintQuestion tq;
		
		if (!isInitial) tq = new TaintQuestion(sp, isInitial, originTq.getOriSourcep());
		else tq = new TaintQuestion(sp, isInitial, sp);
//		if (originTq != null) {
//			tq.setSourcep(originTq.getSourcep());	// For incremental question
//		}
		
		SinkMethod sm;

		for (String str : runTest.sinkMetds) {
			try {
				sm = new SinkMethod(Scene.v().getMethod(str));
				tq.addSinks(sm);
			} catch (Exception e) {
				e.printStackTrace();
			}
		}

		tqInput.add(0, tq);

		print();
	}
	
	private void generateOneQuestionRC(SootMethod smthd, Block block, Unit unit, Value value, HashSet<String> sField, boolean isInitial, TaintQuestion originTq) {
		HashMap<String, Integer> a = new HashMap<>();

		SourcePoint sp = new SourcePoint(smthd, block, unit, value, sField);

		TaintQuestion tq;
		
		if (!isInitial) tq = new TaintQuestion(sp, isInitial, originTq.getOriSourcep(), true);
		else tq = new TaintQuestion(sp, isInitial, sp, true);
//		if (originTq != null) {
//			tq.setSourcep(originTq.getSourcep());	// For incremental question
//		}
		
		SinkMethod sm;

		for (String str : runTest.sinkMetds) {
			try {
				sm = new SinkMethod(Scene.v().getMethod(str));
				tq.addSinks(sm);
			} catch (Exception e) {
				e.printStackTrace();
			}
		}

		tqInput.add(0, tq);

		print();
	}
	
	public void generateOneFindKeyQuestion(SootMethod smthd, Block block, Unit unit, Value value, boolean isInitial, boolean isFinding) {
		ArrayList<String> sinkMetds = new ArrayList<String>();
		
//		sinkMetds.add("<android.content.SharedPreferences: String getString(java.lang.String,java.lang.String)>");
//		sinkMetds.add("<android.content.SharedPreferences: java.util.Set getStringSet(java.lang.String,java.util.Set)>");
		if (!isFinding) sinkMetds = runTest.sinkMetds;
		HashMap<String, Integer> a = new HashMap<>();

		SourcePoint sp = new SourcePoint(smthd, block, unit, value, null);

		TaintQuestion tq = new TaintQuestion(sp, isInitial, sp, true);
//		if (originTq != null) {
//			tq.setSourcep(originTq.getSourcep());	// For incremental question
//		}
		
		SinkMethod sm;

		for (String str : sinkMetds) {
			try {
				sm = new SinkMethod(Scene.v().getMethod(str));
				tq.addSinks(sm);
			} catch (Exception e) {
				e.printStackTrace();
			}
		}

		tqInput.add(0, tq);	// solved first

		print();
	}
	
	public TaintQuestion generateOneStaticFieldQuestion(SootMethod smthd, Block block, Unit unit, Value value, boolean isInitial, TaintQuestion originTq) {
		HashMap<String, Integer> a = new HashMap<>();
		

		SourcePoint sp = new SourcePoint(smthd, block, unit, value, null);

		TaintQuestion tq = new TaintQuestion(sp, isInitial, originTq.getOriSourcep());
//		tq.setSourcep(originTq.getSourcep());
		
		SinkMethod sm;

		for (String str : runTest.sinkMetds) {
			try {
				sm = new SinkMethod(Scene.v().getMethod(str));
				tq.addSinks(sm);
			} catch (Exception e) {
				e.printStackTrace();
			}
		}

		return tq;
	}
	
	public void generateOneIncremtInputQuestion(String funcName, TaintQuestion originTq, HashMap<Integer, HashSet<String>> taintedParam){
		if (runTest.inputMetds.contains(funcName)) {
			HashSet<Integer> taintedVarIndex= runTest.inputMetds2TaintedVar.get(funcName);
			boolean flag = true;
			for (int i : taintedParam.keySet())
				if (!taintedVarIndex.contains(i)) {
					flag = false;
					taintedVarIndex.add(i);
				}
			if (flag) return;
		} else {
			runTest.inputMetds.add(funcName);
			HashSet<Integer> taintedVarIndex= new HashSet<>();
			for (int i : taintedParam.keySet())
				taintedVarIndex.add(i);
			runTest.inputMetds2TaintedVar.put(funcName, taintedVarIndex);
		}
		
		System.out.println("Generating incremental source: " + funcName);
		
		for (SootClass sclas : Scene.v().getClasses()) {
			for (SootMethod smthd : ListUtility.clone(sclas.getMethods())) {
				if (!smthd.isConcrete())
					continue;

				Body body = smthd.retrieveActiveBody();
				if (body == null)
					continue;
				
				
				
				List<Block> bs = BlockGenerator.getInstance().generate(body).getBlocks();
				
				for (Block block : bs) {
					for (Unit unit : block) {
						if (unit instanceof AssignStmt) {
							if (((AssignStmt) unit).getRightOp() instanceof InvokeExpr) {
								InvokeExpr invokeExpr = (InvokeExpr)(((AssignStmt) unit).getRightOp());
								if (funcName.equals(invokeExpr.getMethodRef().getSignature())){
									System.out.println("Found one source: " + unit.toString() + " in " + smthd.getSignature());
									for (Entry<Integer, HashSet<String>> mapElement : taintedParam.entrySet()) {
										int varIndex = mapElement.getKey();
										if (varIndex == -2)
											generateOneQuestion(smthd, block, unit, ((AssignStmt) unit).getLeftOp(), mapElement.getValue(), false, originTq);	// interest in the left op
										else if (varIndex == -1)
											generateOneQuestion(smthd, block, unit, ((InstanceInvokeExpr) invokeExpr).getBase(), mapElement.getValue(), false, originTq);	// interest in the base
//										else  if (varIndex >= 0)
//											generateOneQuestion(tqInput, smthd, block, unit, invokeExpr.getArg(varIndex), mapElement.getValue(), false, originTq);	// interest in the args
							        }
								}

							}
						} else if (unit instanceof InvokeStmt) {
							InvokeExpr invokeExpr = ((InvokeStmt)unit).getInvokeExpr();
							if (funcName.equals(invokeExpr.getMethodRef().getSignature())){
								System.out.println("Found one source: " + unit.toString() + " in " + smthd.getSignature());
								for (Entry<Integer, HashSet<String>> mapElement : taintedParam.entrySet()) {
									int varIndex = mapElement.getKey();
									if (varIndex == -1)
										generateOneQuestion(smthd, block, unit, ((InstanceInvokeExpr) invokeExpr).getBase(), mapElement.getValue(), false, originTq);	// interest in the base
//									else  if (varIndex >= 0)
//										generateOneQuestion(tqInput, smthd, block, unit, invokeExpr.getArg(varIndex), mapElement.getValue(), false, originTq);	// interest in the args
						        }
							}

							
						}
					}
				}
			}
		}
		
		System.out.println("Finish generating one incremental question for one new source: " + funcName);
		System.out.println("Current question number: " + tqInput.size());
	}
	
	public void addFindPfGetAsQstn(String key, TaintQuestion originTq) {
		if (runTest.searchedKeys.contains(key))
			return;
		
		runTest.searchedKeys.add(key);
		
//		System.out.println("**********Searching use of :" + key);
		
		for (SootClass sclas : Scene.v().getClasses()) {
			for (SootMethod smthd : ListUtility.clone(sclas.getMethods())) {
				if (!smthd.isConcrete())
					continue;

				Body body = smthd.retrieveActiveBody();
				if (body == null)
					continue;
				
				
				
				List<Block> bs = BlockGenerator.getInstance().generate(body).getBlocks();
				
				for (Block block : bs) {
					for (Unit unit : block) {
						if (unit instanceof AssignStmt) {
							if (((AssignStmt) unit).getRightOp() instanceof InvokeExpr) {
								InvokeExpr invokeExpr = (InvokeExpr)(((AssignStmt) unit).getRightOp());
								if (containsKey(key, invokeExpr.getArgs())){
//									System.out.println("*******Find key: " + invokeExpr.toString());
//									
									if (!invokeExpr.toString().contains("<java.util.HashMap: java.lang.Object get(java.lang.Object)>")
											&& !invokeExpr.toString().contains("<org.json.JSONObject: java.lang.Object opt"))
										generateOneQuestionRC(smthd, block, unit, ((AssignStmt) unit).getLeftOp(), null, false, originTq);	// interest in the left op
//									else {
//										generateFindKeyQuestion(tqInput, key, invokeExpr.getArgs(), invokeExpr.getMethod());
//									}
								}

							}
						} else if (unit instanceof InvokeStmt) {
							InvokeExpr invokeExpr = ((InvokeStmt)unit).getInvokeExpr();
							
							if (containsKey(key, invokeExpr.getArgs())){
//								System.out.println("*******Find key: " + invokeExpr.toString());
								generateFindKeyQuestion(key, invokeExpr.getArgs(), invokeExpr.getMethod());
							}
						}
					}
				}
			}
		}
		
		System.out.println("Finish generating one incremental question for one new source: " + key);
		System.out.println("Current question number: " + tqInput.size());
	}
	
	boolean containsKey(String key, List<Value> params) {
		for (Value val : params)
			if (val instanceof StringConstant && ((StringConstant) val).value.equals(key))
				return true;
		return false;
	}
	
	void generateFindKeyQuestion(String key, List<Value> params, SootMethod targetMthd) {
		int idx = -1;
		for (Value val : params)
			if (val instanceof StringConstant && ((StringConstant) val).value.equals(key)) {
				idx = params.indexOf(val);
			}
		
		if (idx == -1) 
			return;
		
		if (!targetMthd.isConcrete())
			return;
		
		Body body = targetMthd.retrieveActiveBody();
		if (body == null)
			return;
		
		List<Block> bs = BlockGenerator.getInstance().generate(body).getBlocks();
		for (Block block : bs) {
			for (Unit unit : block) {
				if (unit instanceof IdentityStmt) {
					if (((IdentityStmt)unit).getRightOp() instanceof ParameterRef
							&& (((ParameterRef)((IdentityStmt)unit).getRightOp())).getIndex()==idx)
						generateOneFindKeyQuestion(targetMthd, block, unit, ((IdentityStmt)unit).getLeftOp(), false, true);
				}
			}
		}
	}
	

	public void solveInputQuestions(boolean gArrayQuestions) {
		solvedInput = new ArrayList<TaintQuestion>();

		Hashtable<Integer, ArrayList<TaintQuestion>> solvedList = new Hashtable<Integer, ArrayList<TaintQuestion>>();
		
		TaintQuestionSolver tgSolver = new TaintQuestionSolver();
		int i = 0;
		int positive = 0;
		TaintQuestion tq = null;
		while (getTqInput().size() > 0 && !runTest.timeout){
			tq = getTqInput().get(0);
			getTqInput().remove(0);
			System.out.println("============= Start Solving Q-" + i + ". Now tq size: " + getTqInput().size());
			System.out.println(tq.getSourcep().getMethodLocation());
//			System.out.println(tq.getSourcep().getBlockLocation());
			System.out.println("Source method in: " + tq.getSourcep().getMethodLocation().toString());
			System.out.println("Instruction: " + tq.getSourcep().getInstructionLocation().toString());
			ArrayList<TaintQuestion> solvedtqs = tgSolver.solve(tq);
			System.out.println("============= End Solving Q-"+i);
//			System.out.println("End Solving Q-" + i++);
			i++;
			if (containsPositive(solvedtqs)) {
				solvedList.put(i, solvedtqs);
				positive++;
				runTest.init_taint_res = TResSolve.saveSolved(solvedList);
			}else{
//				System.out.println("Question Q-"+ i + " is negative!\n");
			}
		}

		System.out.println("Statistic: Total Questions:" + i + " Total Positive: " + positive);
		
		
//		Hashtable<Unit, List<SimulationContext>> pointsInput = new Hashtable<Unit, List<SimulationContext>>();
//		for (int idx : solvedList.keySet()) {
//			for (TaintQuestion tq1 : solvedList.get(idx))
//			for (SimulationContext sc : tq1.getsContexts()) {
//				if (sc.isContainsSink()) {
////					System.out.println("========s========");
//					for (StmtItem stmt : sc.getInstructionTrace()) {
//						if (stmt.isContainsSink()) {
//							if (!pointsInput.containsKey(stmt.getU()))
//								pointsInput.put(stmt.getU(), new ArrayList<SimulationContext>());
//							pointsInput.get(stmt.getU()).add(sc);
//							
//						}
////						System.out.println(stmt.getU().toString());
//					}
//				}
//			}
//		}

//		return TResSolve.saveSolved(solvedList);

	}
	
	public boolean containsPositive(ArrayList<TaintQuestion> tqList) {
		for (TaintQuestion tq : tqList)
			if (tq.isPositive()) return true;
		return false;
	}

//	@SuppressWarnings("unchecked")
//	public QuestionGenerator generateArrayQuestions(List<TaintQuestion> solved) {
//		HashSet<SootMethod> sms = new HashSet<SootMethod>();
//
//		ArrayList<StmtItem> stmts;
//		for (TaintQuestion tq : solved) {
//			for (SimulationContext sc : tq.getsContexts()) {
//				if (sc.isContainsSink()) {
//
//					stmts = (ArrayList<StmtItem>) sc.getInstructionTrace().clone();
//
//					while (!stmts.get(stmts.size() - 1).isContainsInteresting())
//						stmts.remove(stmts.size() - 1);
//
//					for (StmtItem stmt : stmts)
//						sms.add(stmt.getSm());
//				}
//			}
//		}
//
//		for (SootMethod smthd : sms) {
//			if (!smthd.isConcrete())
//				continue;
//			Body body = smthd.retrieveActiveBody();
//			if (body == null)
//				continue;
//
//			List<Block> bs = BlockGenerator.getInstance().generate(body).getBlocks();
//
//			for (Block block : bs) {
//				for (Unit unit : block) {
//					if (unit instanceof AssignStmt) {
//						if (((AssignStmt) unit).getRightOp() instanceof JArrayRef) {
//							if (((JArrayRef) ((AssignStmt) unit).getRightOp()).getType().toString().equals("java.lang.String"))
//								generateOneQuestion(tqArray, smthd, block, unit, ((AssignStmt) unit).getLeftOp(), true, null); // not used
//						}
//					}
//				}
//			}
//		}
//
//		return this;
//	}

	public void solveArrayQuestions() {

		TaintQuestionSolver tgSolver = new TaintQuestionSolver();
		int i = 0;
		int positive = 0;
		for (TaintQuestion tq : getTqArray()) {
			System.out.println("aaa");
			System.out.println(tq.getSourcep().getMethodLocation());
			System.out.println(tq.getSourcep().getBlockLocation());
			System.out.println("aaa");
			tgSolver.solve(tq);
			System.out.println("ddd " + i++);

			if (tq.isPositive()) {
				solvedArray.add(tq);
				System.out.println("positive!");
				positive++;
			}
		}

		System.out.println("ddd " + i + " " + positive);

	}

	public ArrayList<CrossPath> checkOverlappingAndGetResults() {
		ArrayList<CrossPath> paths = new ArrayList<CrossPath>();
		if (solvedInput.size() > 0 && solvedArray.size() > 0) {
			Hashtable<Unit, List<SimulationContext>> pointsInput = new Hashtable<Unit, List<SimulationContext>>();
			Hashtable<Unit, List<SimulationContext>> pointsArray = new Hashtable<Unit, List<SimulationContext>>();

			for (TaintQuestion tq : solvedInput) {
				for (SimulationContext sc : tq.getsContexts()) {
					if (sc.isContainsSink()) {
						for (StmtItem stmt : sc.getInstructionTrace()) {
							if (stmt.isContainsSink()) {
								if (!pointsInput.containsKey(stmt.getU()))
									pointsInput.put(stmt.getU(), new ArrayList<SimulationContext>());
								pointsInput.get(stmt.getU()).add(sc);
							}
						}
					}
				}
			}

			for (TaintQuestion tq : solvedArray) {
				for (SimulationContext sc : tq.getsContexts()) {
					if (sc.isContainsSink()) {
						for (StmtItem stmt : sc.getInstructionTrace()) {
							if (stmt.isContainsSink()) {
								if (!pointsArray.containsKey(stmt.getU()))
									pointsArray.put(stmt.getU(), new ArrayList<SimulationContext>());
								pointsArray.get(stmt.getU()).add(sc);
							}
						}
					}
				}
			}

			for (Unit u : pointsInput.keySet()) {
				if (pointsArray.containsKey(u)) {
					paths.add(new CrossPath(u, pointsInput.get(u), pointsArray.get(u)));
				}
			}

		}

		System.out.println(paths.size());

		return paths;
	}

	public QuestionGenerator print() {
		Logger.print("tqInput size:" + tqInput.size());
		Logger.print("tqArray size:" + tqArray.size());
		return this;
	}

	public ArrayList<TaintQuestion> getTqInput() {
		return tqInput;
	}

	public ArrayList<TaintQuestion> getTqArray() {
		return tqArray;
	}

}
