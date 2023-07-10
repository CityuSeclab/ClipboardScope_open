package clipboardscope.taintanalysis.solver;

import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.ListIterator;
import java.util.Scanner;
import java.util.Set;
import java.util.Spliterators.AbstractSpliterator;

import javax.management.InstanceNotFoundException;

import java.util.Map.Entry;
import java.util.PrimitiveIterator.OfDouble;

import org.apache.commons.lang3.concurrent.ConcurrentException;
import org.hamcrest.core.Is;
import org.hamcrest.core.IsInstanceOf;
import org.jf.util.IndentingWriter;
import org.jf.util.TextUtils;
import org.junit.experimental.theories.internal.Assignments;
import org.junit.internal.InexactComparisonCriteria;
import org.junit.internal.runners.statements.InvokeMethod;

import com.beust.jcommander.Parameter;
import com.google.common.io.BaseEncoding;

import clipboardscope.main.runTest;
import clipboardscope.taintanalysis.base.TaintQuestion;
import clipboardscope.taintanalysis.utility.BlockGenerator;
import clipboardscope.taintanalysis.utility.ListUtility;
import clipboardscope.taintanalysis.utility.Logger;
import clipboardscope.taintanalysis.utility.MethodUtility;
import soot.Body;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.JastAddJ.Stmt;
import soot.baf.IfCmpEqInst;
import soot.dava.toolkits.base.renamer.heuristicSet;
import soot.grimp.NewInvokeExpr;
import soot.jimple.AbstractStmtSwitch;
import soot.jimple.ArrayRef;
import soot.jimple.AssignStmt;
import soot.jimple.CastExpr;
import soot.jimple.CaughtExceptionRef;
import soot.jimple.DefinitionStmt;
import soot.jimple.FieldRef;
import soot.jimple.IdentityStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InterfaceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.NewExpr;
import soot.jimple.ParameterRef;
import soot.jimple.ReturnStmt;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.StaticFieldRef;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.StringConstant;
import soot.jimple.ThisRef;
import soot.jimple.VirtualInvokeExpr;
import soot.jimple.infoflow.rifl.RIFLDocument;
import soot.jimple.internal.JArrayRef;
import soot.jimple.internal.JInterfaceInvokeExpr;
import soot.toolkits.graph.Block;
import soot.toolkits.graph.CompleteBlockGraph;

public class SimulationEngine extends AbstractStmtSwitch {
	int print_count = 0;
	int maxInvokeLayer = 6;
	static SimulationEngine se = new SimulationEngine();
	InvokeExpr currentMultiThrdFunc = null;
	HashMap<Integer, HashSet<String>> taintToMultiThrdFunc = null;

	private void pauseWhile() {
		System.out.println("Press enter to continue");
		try{System.in.read();}
		catch(Exception e){}
	}
	
	private SimulationEngine() {
	}

	public static SimulationEngine getInstance() {
		return se;
	}

	TaintQuestion tq;

	public List<SimulationContext> oneStepForward(TaintQuestion tq, SimulationContext sContext) {
		this.tq = tq;
		Unit nextInstrct = null;
		if (sContext.getInstructionLocation() == null) {
			nextInstrct = sContext.getBlockLocation().getHead();
		} else {
			nextInstrct = sContext.getBlockLocation().getSuccOf(sContext.getInstructionLocation());
		}
		Logger.print("nextInstrct: " + nextInstrct + "");
		if (nextInstrct != null) {
			return oneStepForward(tq, sContext, nextInstrct);
		} else {
			Logger.print(sContext.getBlockLocation().getIndexInMethod() + "=>>");
			List<Block> processableBlocks = getProcessableBlocks(sContext);
			for (Block b : sContext.getBlockTrace())
				Logger.print("t:" + b.getIndexInMethod() + "\t" + b.getBody().getMethod());
			for (Block b : processableBlocks)
				Logger.print(b.getIndexInMethod() + "");
			// if(processableBlocks.size() !=
			// sContext.getBlockLocation().getSuccs().size())
			// System.exit(0);
			if (!processableBlocks.isEmpty()) {
				return oneStepForward2EachBlock(tq, sContext, processableBlocks);
			} else {
				// backtofunc
				sContext.setTerminated(true);
			}
		}

		return new ArrayList<SimulationContext>();
	}

	private List<Block> getProcessableBlocks(SimulationContext sContext) {
		List<Block> allBlocks = sContext.getBlockLocation().getSuccs();
		List<Block> bs = new ArrayList<Block>();
		Block tmp;
		boolean canprocess;
		for (Block block : allBlocks) {
			canprocess = true;
			HashSet<Block> hist = new HashSet<Block>();
			ListIterator<Block> li = sContext.getBlockTrace().listIterator(sContext.getBlockTrace().size());
			li.previous();// skip current
			while (li.hasPrevious()) {
				tmp = li.previous();
				if (!tmp.getBody().equals(sContext.getBlockLocation().getBody()))
					break;

				if (tmp == block) {
					if (hist.contains(tmp)) {
						canprocess = false;
						break;
					} else
						hist.add(block);
				}
			}

			if (canprocess)
				bs.add(block);
		}
		return bs;
	}

	private List<SimulationContext> oneStepForward2EachBlock(TaintQuestion tq, SimulationContext sContext,
			List<Block> processableBlocks) {
		List<SimulationContext> newBc = new ArrayList<SimulationContext>();
		List<Block> sBlocks = processableBlocks;// sContext.getBlockLocation().getSuccs();

		for (int i = 1; i < sBlocks.size(); i++) {
			SimulationContext tsc = new SimulationContext(sContext);
			tsc.setBlockLocation(sBlocks.get(i));

			newBc.add(tsc);
			newBc.addAll(oneStepForward(tq, tsc, tsc.getBlockLocation().getHead()));
		}

		sContext.setBlockLocation(sBlocks.get(0));
		newBc.addAll(oneStepForward(tq, sContext, sContext.getBlockLocation().getHead()));

		return newBc;
	}

	SimulationContext sContext;

	private List<SimulationContext> oneStepForward(TaintQuestion tq, SimulationContext sContext,
			Unit currentInstruction) {
		this.sContext = sContext;
		List<SimulationContext> newBc = new ArrayList<SimulationContext>();

		
		for (CallStackItem csi : sContext.getCallStack()) {
			Logger.print("    " + csi.getSmethd());
		}

		// for (Value value : sContext.getIntrestedVariable()) {
		// Logger.print("iv:" + value);
		// }
		boolean containsIntrestedThings = false;
		
		sContext.resetCurInterestedVariable();
		
		for (ValueBox box : currentInstruction.getUseAndDefBoxes()) {
			// To track the param reachability, only processed in AssignStmt
			if (this.sContext.isIntrested(box.getValue())) {
				containsIntrestedThings = true;
				sContext.addCurInterestedVariable(box.getValue());
//				System.out.println("In Value " + box.getValue());
//				sContext.setInstructionLocation(currentInstruction, containsIntrestedThings, box.getValue());
//				break;
			}
		}

		sContext.setInstructionLocation(currentInstruction, containsIntrestedThings);
		

//		System.out.println("Cur tainted var: " + sContext.getIntrestedVariable());
		
		
		if (currentInstruction instanceof DefinitionStmt) 
			this.sContext.insertOneDefStmtToCash((DefinitionStmt) currentInstruction);
		
		// for network checking
		if (currentInstruction.toString().contains("java.net") && currentInstruction.toString().contains("getOutputStream()")) {
			this.sContext.add2InstructionTraceSink(sContext.getMethodLocation(), sContext.getBlockLocation(), currentInstruction, true);
		}
		
		if (!containsIntrestedThings && !(currentInstruction instanceof ReturnStmt)
				&& !(currentInstruction instanceof ReturnVoidStmt)
				&& !(currentInstruction instanceof IdentityStmt))
			return newBc;
		
		sContext.add2InstructionTrace(sContext.getMethodLocation(), sContext.getBlockLocation(), currentInstruction,
				containsIntrestedThings);

		
//		System.out.println("Cur Inst: " + currentInstruction);
		
		
		currentInstruction.apply(this);

		return newBc;
	}

	// InstanceInvokeExpr
	public boolean handleInvokeStmt(Value assiTo, InvokeExpr invokExpr) {
		
//		pauseWhile();
		Value base = null;
		boolean interestinRet = false;
		if (invokExpr instanceof InstanceInvokeExpr) base = ((InstanceInvokeExpr) invokExpr).getBase();
		boolean isInterestedInArgs = this.sContext.containsIntrested(invokExpr.getArgs());
		boolean isInterestedInBase = base == null ? false : this.sContext.isIntrested(base);

		
		if (!isInterestedInArgs && !isInterestedInBase) return false;
//		if (!isInterestedInArgs) return false;

		if (tq.isSink(invokExpr.getMethod())) {
//			System.out.println("++++++Found leak at: " + invokExpr.toString() + "\nLayer: " + this.sContext.invokeLayer + " Intrested in " + this.sContext.getCurInterestedVariable());
			this.sContext.setContainsSink(true, this.sContext.getCurInterestedVariable());
			
			if ((invokExpr.getMethod().getSignature().equals("<android.content.SharedPreferences$Editor: android.content.SharedPreferences$Editor putString(java.lang.String,java.lang.String)>")
					|| invokExpr.getMethod().getSignature().equals("<android.content.SharedPreferences$Editor: android.content.SharedPreferences$Editor putStringSet(java.lang.String,java.util.Set)>")
					|| invokExpr.getMethod().getSignature().contains("putExtra"))
					&& this.sContext.isIntrested(invokExpr.getArg(1))) {
				String key = getHardCodedKey(invokExpr.getArg(0));
				if (!key.isEmpty()) {
					// Find a callsite with key as param
					runTest.qg.addFindPfGetAsQstn(key, this.tq);
				}
			
			}
		}
		
		
		if (tq.getSinks().size() == 0 && isInterestedInArgs
				&& !invokExpr.toString().contains("<java.util.HashMap: java.lang.Object get(java.lang.Object)>")
				&& !invokExpr.toString().contains("<org.json.JSONObject: java.lang.Object opt")) {
			if (assiTo != null) {
//				System.out.println("*******Found return key ***********");
				runTest.qg.generateOneFindKeyQuestion(this.sContext.getMethodLocation(), this.sContext.getBlockLocation(), 
						this.sContext.getInstructionLocation(), assiTo, false, false);
				if (this.sContext.isIntrested(assiTo)) {
					this.sContext.getIntrestedVariable().clear();
					return false;
				}
			}
		}
		
		
//		 These are all for asynchronized calls
			
		if (isInterestedInArgs){
			currentMultiThrdFunc = invokExpr;
			taintToMultiThrdFunc = getTaintByMultiThrdFunc();
			
			if (invokExpr.getMethod().toString().contains("<android.os.Message: android.os.Message obtain(android.os.Handler")) {
				trackMultiThrdTaint(invokExpr.getArg(0));
				return false;
			}
			if (invokExpr.getMethod().toString().contains("<android.os.Handler: boolean sendMessage(android.os.Message")
					|| invokExpr.getMethod().toString().contains("<android.os.Handler: boolean sendMessageAtTime(android.os.Message")
					|| invokExpr.getMethod().toString().contains("<android.os.Handler: boolean sendMessageDelayed(android.os.Message")) {
				if (base != null) trackMultiThrdTaint(base);
				else System.out.println("******Error with null base..");
				return false;
			}
			// ==========================================================
			if (invokExpr.getMethod().toString().contains("post(java.lang.Runnable)")	// Handler post
					|| invokExpr.getMethod().toString().contains("execute(java.lang.Runnable)")	// Asyntask/concurrentService execute
					|| invokExpr.getMethod().toString().contains("postDelayed(java.lang.Runnable")	// Handler postDelayed
					|| invokExpr.getMethod().toString().contains("<init>(java.lang.Runnable)")) {	// Thread initialization
				// All method with Runnable as the first arg
				trackMultiThrdTaint(invokExpr.getArg(0));
				return false;
			}
			
			if (invokExpr.getMethod().toString().contains("java.lang.Thread: void start()")) {
				// All method with Runnable as the first arg
				if (base != null) trackMultiThrdTaint(base);
				return false;
			}
			
			// ========================================
			if (invokExpr.getMethod().toString().contains("android.os.AsyncTask execute(java.lang.Object[])>")) {
//				System.out.println("*****Found execute(java.lang.Object[])..." + this.sContext.getMethodLocation());
				if (base != null) trackMultiThrdTaint(base);
				else System.out.println("******Error with null base..");
				return false;
			}
			if (invokExpr.getMethod().toString().contains("void publishProgress(java.lang.Object[])>"))
				if (sContext.getMethodLocation().toString().contains(" doInBackground(")){
					SootMethod targetMthd = null;
					targetMthd = sContext.getMethodLocation().getDeclaringClass().getMethod("void onProgressUpdate(java.lang.Object[])");
//					System.out.println("******TargetMthd:" + targetMthd);
					if (targetMthd != null) {
						jump2Mthd(targetMthd, true);
					}
					return false;
				}
				
		}
//		
//		System.out.println("Normal invoke");
		
		boolean taintBase = false, taintRet = false;
		String invokString = invokExpr.toString().toLowerCase();
		if ((isInterestedInArgs || isInterestedInBase)	// If with params or base of interest
				 && invokExpr.getMethod().getDeclaringClass().isApplicationClass()
				 && invokExpr.getMethod().isConcrete()) {	// If user-defined concrete methods
					if (invokString.contains("encrypt") || invokString.contains("encode")
							|| invokString.contains("create") || invokString.contains("parse") 
							|| invokString.contains("tojson") || invokString.contains("tostring")) {
						interestinRet = true;
						if (assiTo != null) {
							sequentialRemoveFieldFrom(assiTo);
							propagateTaintFieldFrom(assiTo, null);
						}
						if (base != null) {
							sequentialRemoveFieldFrom(base);
							propagateTaintFieldFrom(base, null);
						}
					} else if (this.sContext.invokeLayer < maxInvokeLayer && isInterestedInArgs) 
						this.jump2callee(assiTo, invokExpr);
					else {	// If not go in to the func, default interest in return
//						System.out.println("Not invoking " + invokExpr.getMethod().toString() + ", since exceeding the maximum layer of invoke.");
						interestinRet = true;
	//					this.sContext.addIntrestedVariable(base, null);
						if (base != null) {
							sequentialRemoveFieldFrom(base);
							propagateTaintFieldFrom(base, null);
						}
						if (assiTo != null) {
							sequentialRemoveFieldFrom(assiTo);
							propagateTaintFieldFrom(assiTo, null);
						}
					}
			} else if (isInterestedInArgs || isInterestedInBase) {
				if (!invokExpr.getMethod().getDeclaringClass().isApplicationClass()
						&& invokExpr.getMethod().getReturnType().toString() != "boolean") { // If it is not an application class, interest in return
					interestinRet = true;
					if (base != null && !isInterestedInBase) {
						propagateTaintFieldFrom(base, null);
					}
					if (assiTo != null) {
						sequentialRemoveFieldFrom(assiTo);
						propagateTaintFieldFrom(assiTo, null);
					}
					
				} else if (invokExpr.getMethod().getDeclaringClass().isApplicationClass()){	//interface invoke
//					if (this.sContext.invokeLayer < maxInvokeLayer && isInterestedInArgs){
//						this.jump2callee(assiTo, invokExpr);	// Not consider interface invoke
//					} else {	// If not go in to the func, default interest in return
//						System.out.println("Not invoking " + invokExpr.getMethod().toString() + ", since exceeding the maximum layer of invoke.");
						interestinRet = true;
						if (base != null) {
							sequentialRemoveFieldFrom(base);
							propagateTaintFieldFrom(base, null);
						}
						if (assiTo != null) {
							sequentialRemoveFieldFrom(assiTo);
							propagateTaintFieldFrom(assiTo, null);
						}
						
//					}
				}
			} else
				defaultCase(invokExpr);
		return interestinRet;
	}
	
	public HashMap<Integer, HashSet<String>> getTaintByMultiThrdFunc() {
		HashMap<Integer, HashSet<String>> taintParam = new HashMap<>();
		HashSet<String> sField = new HashSet<>();
		String mthdName = currentMultiThrdFunc != null ? currentMultiThrdFunc.getMethod().toString() : null;
		if (mthdName == null) {	// In special return case
			if (sContext.getMethodLocation().getName().equals("doInBackground")) {
				// --> void onPostExecute(java.lang.Object)
				sField.addAll(this.sContext.getTaintedParams().get(-2));
				taintParam.put(0, sField);
				return taintParam;
			}
			return null;
		}
		
		if (mthdName.contains("<android.os.Message: android.os.Message obtain(android.os.Handler")) {
			// --> handleMessage(Message msg)
			sField.add("<android.os.Message: java.lang.Object obj>");
			taintParam.put(0, sField);
			return taintParam;
		}
		if (mthdName.contains("(android.os.Message")) {
			// --> handleMessage(Message msg)
			sField.add("<android.os.Message: java.lang.Object obj>");
			taintParam.put(0, sField);
			return taintParam;
		}
		if (mthdName.contains("(java.lang.Runnable")) {	// All with Runnable as the first arg, including initialization of Thread(Runnable)
			// --> run()
			sField.addAll(this.sContext.getIntrestedVariable().get(getBaseValue(currentMultiThrdFunc.getArg(0))));
			taintParam.put(-1, sField);
			return taintParam;
		}
//		if (mthdName.contains("java.lang.Thread: void start()")) {
//			if (currentMultiThrdFunc instanceof InstanceInvokeExpr) {
//				sField.addAll(this.sContext.getIntrestedVariable().get(((InstanceInvokeExpr)currentMultiThrdFunc).getBase()));
//				taintParam.put(-1, sField);
//				return taintParam;
//			}
//		}
		if (mthdName.contains("android.os.AsyncTask execute(java.lang.Object[])>")) {
			// --> doInBackground(java.lang.Object[])
			sField.addAll(this.sContext.getIntrestedVariable().get(getBaseValue(currentMultiThrdFunc.getArg(0))));
			taintParam.put(0, sField);
			return taintParam;
		}
		if (mthdName.contains("void publishProgress(java.lang.Object[])>")) {
			// void onProgressUpdate(java.lang.Object[])
			sField.addAll(this.sContext.getIntrestedVariable().get(getBaseValue(currentMultiThrdFunc.getArg(0))));
			taintParam.put(0, new HashSet<String>());
			return taintParam;
		}
		return null;
	}
	
	public void jump2Mthd(SootMethod targetMthd, boolean needPop) {	// Special case for indirect invocation
		if (targetMthd == null) return;
		CallStackItem citem = new CallStackItem(this.sContext.getMethodLocation(), this.sContext.getBlockLocation(), 
				this.sContext.getInstructionLocation(), null, this.MultiThrdInvoke, true, new HashMap<Value, HashSet<String>>(), null, 
				this.sContext.getParam2Var(), this.sContext.getCashedAssignStmt());	// caller site
		
		Value taintVar = null;
//		System.out.println("taintToMultiThrdFunc: " + taintToMultiThrdFunc);
		for (Entry<Integer, HashSet<String>> mapElement : taintToMultiThrdFunc.entrySet()) {
			if (mapElement.getKey() >= 0) {
				taintVar = MethodUtility.getParameterRef(targetMthd, mapElement.getKey());
				this.sContext.addIntrestedVariable(taintVar, mapElement.getValue());
			} else {
				taintVar = MethodUtility.getThisRef(targetMthd);
				this.sContext.addIntrestedVariable(taintVar, mapElement.getValue());
			}
        }
		
//		System.out.println("*****jump2callee: " + citem.getSmethd().toString());
		if (needPop) this.sContext.getCallStack().push(citem);
		
		Body body = targetMthd.retrieveActiveBody();
		CompleteBlockGraph cbg = BlockGenerator.getInstance().generate(body);
		if (cbg.getHeads().size() > 1) {  
			System.out.println("header size > 1");
		}
		
		this.sContext.setMethodLocation(targetMthd);
		this.sContext.setBlockLocation(cbg.getHeads().get(0));
		this.sContext.setInstructionLocation(null, false);
		this.sContext.resetCashedAssignStmt();
		this.sContext.invokeLayer++;
	}
	
	@Override
	public void caseInvokeStmt(InvokeStmt stmt) {
		handleInvokeStmt(null, stmt.getInvokeExpr());
	}

	@Override
	public void caseAssignStmt(AssignStmt stmt) {
		// TODO Auto-generated method stub
		
		Value lop = getValue(stmt.getLeftOp());
		Value rop = getValue(stmt.getRightOp());
		
		
		boolean interestinRet = false;
		
		
		
		if (rop instanceof InvokeExpr) {
			interestinRet = handleInvokeStmt(lop, stmt.getInvokeExpr());
		} else if (this.sContext.isIntrested(rop) && (rop instanceof InstanceFieldRef) && !(lop instanceof FieldRef)) {
			// ri = rj.<Field> ...... ri <- ri.<FieldSet \ <Field>>
			interestinRet = true;
			sequentialRemoveFieldFrom(lop);
			this.sContext.addIntrestedVariable(getBaseValue(lop), 
					diffWithField(this.sContext.getIntrestedVariable().get(getBaseValue(rop)), ((InstanceFieldRef)rop).getField().toString()));
		} 
		else if (this.sContext.isIntrested(rop)){		// TODO: If rop is a FieldRef, propagate the subfield to lop
			interestinRet = true;
			sequentialRemoveFieldFrom(lop);
			propagateTaintFieldFrom(lop, null);
			
		} else {
			defaultCase(stmt);
		}
		
//		this.sContext.removeIntrestedVariable(lop, null);
		
		if (!interestinRet)
			sequentialRemoveFieldFrom(lop);
	}


	@Override
	public void caseReturnStmt(ReturnStmt stmt) {
		// TODO Auto-generated method stub
		boolean interestinRet = false;
//		System.out.println("At return cur taint: " + this.sContext.getIntrestedVariable().keySet());
		if (stmt != null && this.sContext.isIntrested(stmt.getOp())) {
			interestinRet = true;
			HashSet<String> returnField = this.sContext.getIntrestedVariable().get(stmt.getOp());
			if (returnField != null){
				HashSet<String> sField = this.sContext.getTaintedParams().containsKey(-2) ? 
						this.sContext.getTaintedParams().get(-2) : new HashSet<String>();
				sField.addAll(returnField);
				this.sContext.getTaintedParams().put(-2, sField);
//				System.out.println("Added -2 " + stmt.getOp() + " " + sField);
			}
			
		}
		List<Type> prefTypeList = this.sContext.getMethodLocation().getParameterTypes();

		
//		getParam2Var() : 0 -- this, 1 ~ N + 1 : param 0 ~ N
		for (int i = 0; i < this.sContext.getParam2Var().size(); i++) {
			if (i >= prefTypeList.size()) break;
			if (i > 0 &&  runTest.ImmutableClass.contains(prefTypeList.get(i - 1).toString()))
				continue;
			if (this.sContext.getIntrestedVariable().containsKey(this.sContext.getParam2Var().get(i))) {
				HashSet<String> sFields = this.sContext.getTaintedParams().containsKey(i - 1) ? 
						this.sContext.getTaintedParams().get(i - 1) : new HashSet<String>(); 
				
				sFields.addAll(this.sContext.getIntrestedVariable().get(this.sContext.getParam2Var().get(i)));
				
				this.sContext.getTaintedParams().put(i - 1, sFields);
			}
		}
		
		if (this.sContext.invokeLayer == 0) getTaintedParamAtStart();	// For the first layer
		
		for (ValueBox vb : this.sContext.getBlockLocation().getBody().getDefBoxes()) {
			this.sContext.intrestedVariable.remove(vb.getValue());
		}
		
		for (ValueBox box : this.sContext.getMethodLocation().retrieveActiveBody().getUseAndDefBoxes()) {
			if (box.getValue() instanceof ParameterRef && this.sContext.getIntrestedVariable().containsKey(box.getValue()))
				this.sContext.intrestedVariable.remove(box.getValue());
			if (box.getValue() instanceof ThisRef && this.sContext.getIntrestedVariable().containsKey(box.getValue()))
				this.sContext.intrestedVariable.remove(box.getValue());
		}
		this.sContext.resetCashedAssignStmt();
		back2caller(interestinRet);
	}

	@Override
	public void caseReturnVoidStmt(ReturnVoidStmt stmt) {
		// TODO Auto-generated method stub
		caseReturnStmt(null);
	}

	@Override
	public void caseIdentityStmt(IdentityStmt stmt) {
		// TODO Auto-generated method stub
//		System.out.println("in identity stmt");
		Value rop = stmt.getRightOp();
		Value lop = stmt.getLeftOp();
		if (rop instanceof ThisRef) {
			this.sContext.getParam2Var().add(lop);
			if (this.sContext.isIntrested(rop))
				this.sContext.addIntrestedVariable(lop, this.sContext.getIntrestedVariable().get(rop));
//			System.out.println("+++++++++Added base ref: " + lop);
		}
		if (rop instanceof ParameterRef) {
			this.sContext.getParam2Var().add(lop);
			if (this.sContext.isIntrested(rop))
				this.sContext.addIntrestedVariable(lop, this.sContext.getIntrestedVariable().get(rop));
		} else
			defaultCase(stmt);
	}

	@Override
	public void defaultCase(Object obj) {
		// TODO Auto-generated method stub
//		System.out.println("unsupported stmt:" + obj);
	}

	// //////////////////////////////////////////////////
	// handle call
	String notAnInterface = "NotAnInterface";
	String MultiThrdInvoke = "MultiThrdInvoke";
	
	private void jump2callee(Value assiTo, InvokeExpr invokExpr) {
//		System.out.println("++++++invoke method: " + invokExpr.toString() + ", current Layer: " + this.sContext.invokeLayer);	
		if (invokExpr.getMethod().isConcrete()){
			CallStackItem citem = new CallStackItem(this.sContext.getMethodLocation(), this.sContext.getBlockLocation(), 
					this.sContext.getInstructionLocation(), assiTo, this.notAnInterface, false, new HashMap<Value, HashSet<String>>(), invokExpr,
					this.sContext.getParam2Var(), this.sContext.getCashedAssignStmt());	// caller site
			
			
			ParameterRef pref;
	
			for (int i = 0; i < invokExpr.getArgs().size(); i++) {
				if (this.sContext.isIntrested(invokExpr.getArgs().get(i))) {
					pref = MethodUtility.getParameterRef(invokExpr.getMethod(), i);
					this.sContext.addIntrestedVariable(pref, this.sContext.getIntrestedVariable().get(invokExpr.getArgs().get(i)));
				}
				
			}
			
			if (invokExpr instanceof InstanceInvokeExpr && this.sContext.isIntrested(((InstanceInvokeExpr)invokExpr).getBase())) {
				ThisRef thisRef = MethodUtility.getThisRef(invokExpr.getMethod());
				this.sContext.addIntrestedVariable(thisRef, this.sContext.getIntrestedVariable().get(((InstanceInvokeExpr)invokExpr).getBase()));
			}
			
//			System.out.println("*****jump2callee: " + citem.getSmethd().toString());
			this.sContext.getCallStack().push(citem);
			
			this.sContext.setMethodLocation(invokExpr.getMethod());
			Body body = this.sContext.getMethodLocation().retrieveActiveBody();
			CompleteBlockGraph cbg = BlockGenerator.getInstance().generate(body);
			// for (Block b : cbg.getHeads()) {
			//
			// }
	
			if (cbg.getHeads().size() > 1) {
				Logger.printW("header size > 1");
			}
			
			
			this.sContext.setParam2Var(new ArrayList<>());
			
			if (invokExpr instanceof StaticInvokeExpr) {	// static invoke have no THIS
				this.sContext.getParam2Var().add(null);
			}
	
			this.sContext.setBlockLocation(cbg.getHeads().get(0));
			this.sContext.setInstructionLocation(null, false);
			this.sContext.invokeLayer++;
			this.sContext.resetCashedAssignStmt();
			
		} else {	// Need to get interface implementations and select one
			
			String interfName = invokExpr.getMethod().getDeclaringClass().toString();
			String curMthdTplt = MethodUtility.getMthdTemplt(invokExpr.getMethod());
			
//			System.out.println("Handling interface invoke: " + interfName + " " + curMthdTplt);
			
			CallStackItem citem = new CallStackItem(this.sContext.getMethodLocation(), this.sContext.getBlockLocation(),
					this.sContext.getInstructionLocation(), assiTo, interfName + curMthdTplt, true, new HashMap<>(), invokExpr,
					this.sContext.getParam2Var(), this.sContext.getCashedAssignStmt());	// return to the caller site
			this.sContext.getCallStack().push(citem);
			
			if (runTest.i2c.containsKey(interfName)){
					for (int i = 0 ; i < runTest.i2c.get(interfName).size(); i++) {
						SootMethod interfMthd = runTest.i2c.get(interfName).get(i);
						if (interfMthd.isConcrete() && MethodUtility.getMthdTemplt(interfMthd).equals(curMthdTplt)) {
//							if (!(interfMthd.getSignature().contains("com.taobao.tao.flexbox.layoutmanager.ac.f$2"))) continue;
							ParameterRef pref;
							HashMap<Value, HashSet<String>> prefList = new HashMap<>();
							
							if (invokExpr instanceof InstanceInvokeExpr && this.sContext.isIntrested(((InstanceInvokeExpr)invokExpr).getBase())) {
								ThisRef thisRef = MethodUtility.getThisRef(interfMthd);
								prefList.put(thisRef, this.sContext.getIntrestedVariable().get(((InstanceInvokeExpr)invokExpr).getBase()));
							}
							
							
							for (int j = 0; j < invokExpr.getArgs().size(); j++) {
								if (this.sContext.isIntrested(invokExpr.getArgs().get(j))) {
									pref = MethodUtility.getParameterRef(interfMthd, j);
									prefList.put(pref, this.sContext.getIntrestedVariable().get(invokExpr.getArgs().get(j)));
								}
							}
							
							
							Body body = interfMthd.retrieveActiveBody();
							CompleteBlockGraph cbg = BlockGenerator.getInstance().generate(body);
							
							citem = new CallStackItem(interfMthd, cbg.getHeads().get(0),
									null, assiTo, interfName + curMthdTplt, false, prefList, invokExpr,
									this.sContext.getParam2Var(), this.sContext.getCashedAssignStmt());	// Add interface method into stack
							this.sContext.getCallStack().push(citem);
							
//							System.out.println("Selected interf Mthd: " + interfMthd.toString());
						}
					}
			
			
				//==========
				
				citem = this.sContext.getCallStack().pop();	// caller site
				
				this.sContext.addAllIntrestedVariable(citem.getInterestedPref());
				
				this.sContext.setMethodLocation(citem.getSmethd());
				
				Body body = this.sContext.getMethodLocation().retrieveActiveBody();
				CompleteBlockGraph cbg = BlockGenerator.getInstance().generate(body);
	
		
				if (cbg.getHeads().size() > 1) {
					System.out.println("header size > 1");
				}
				
				this.sContext.setParam2Var(new ArrayList<>());	//	function invocation, must be instance invoke
				this.sContext.setBlockLocation(cbg.getHeads().get(0));
				this.sContext.setInstructionLocation(null, false);
				this.sContext.resetCashedAssignStmt();
				this.sContext.invokeLayer++;
			}
		}

	}

	private void back2caller(boolean interestinRet) {
//		if (sContext.getMethodLocation().toString().contains("android.net.Uri[] getSelectedFiles(android.content.Intent,int"))
//			System.out.println("Now in func: " + sContext.getMethodLocation().toString() + ". Is interested in return value? " + interestinRet);
		this.sContext.invokeLayer--;
		if (this.sContext.getIntrestedVariable().isEmpty() && this.sContext.getTaintedParams().isEmpty()){
//			System.out.println("*****back2caller: no interested variable in context. CallStack empty? " + Boolean.toString(this.sContext.callStack.isEmpty()));
			this.sContext.setTerminated(true);
		} else {
			if (this.sContext.callStack.isEmpty()) {
//				System.out.println("******back2caller: empty callstack, set termination");
				Logger.printW("unimplemented return to outside");
				if (!this.sContext.getTaintedParams().isEmpty()) {
					runTest.qg.generateOneIncremtInputQuestion(sContext.getMethodLocation().toString(), tq, this.sContext.getTaintedParams());
				}
				this.sContext.setTerminated(true);
			} 
			else if (this.sContext.getMethodLocation().getName().equals("doInBackground") 	// Special case for android.os.AsyncTask
					&& !sContext.getMethodLocation().getReturnType().toString().equals("java.lang.Object")
//					&& sContext.getMethodLocation().getDeclaringClass().getSuperclass().toString().equals("android.os.AsyncTask")
					&& interestinRet){
				SootMethod targetMthd = null;
				targetMthd = sContext.getMethodLocation().getDeclaringClass().getMethod("void onPostExecute(java.lang.Object)");
				currentMultiThrdFunc = null;
				taintToMultiThrdFunc = getTaintByMultiThrdFunc();
//				System.out.println("******TargetMthd:" + targetMthd);
//				System.out.println(taintToMultiThrdFunc);
				this.sContext.getTaintedParams().clear();	// IMPORTANT, it is not a common return, 
															// so need to clean the tainted param here
				jump2Mthd(targetMthd, false);
			} else {
				CallStackItem citem = this.sContext.getCallStack().pop();
				// Add the tainted actual params
				InvokeExpr invokExpr = citem.getInvokeExpr();
				this.sContext.cashedAssgnStmt = citem.getCashedDefStmt();	// resume the caller site Assignments
				
				// Propagate taint back to caller site
				// -2 : return target, -1 : base Obj, >=0 : params
				// Firstly remove the original tainted vars, and then add back the new ones with Fields 
				if (invokExpr != null && !citem.getInterfName().equals(this.MultiThrdInvoke)) {
					List<Value> argList = invokExpr.getArgs();
					for (Entry<Integer, HashSet<String>> mapElement : this.sContext.getTaintedParams().entrySet()) {
						int i = mapElement.getKey();
						HashSet<String> sFields = mapElement.getValue();
						if (i == -1 && invokExpr instanceof InstanceInvokeExpr) { // Base Obj, Include special/virtual/interface invoke
							sequentialRemoveFieldFrom(((InstanceInvokeExpr) invokExpr).getBase());
							propagateTaintFieldFrom(((InstanceInvokeExpr) invokExpr).getBase(), sFields);

						} else if (i == -2 && citem.getReturnTarget() != null) {	// Return Obj
							sequentialRemoveFieldFrom(citem.getReturnTarget());
							propagateTaintFieldFrom(citem.getReturnTarget(), sFields);
						} else if (i >= 0 && i < argList.size()) {
//							sequentialRemoveFieldFrom(argList.get(i));
//							propagateTaintFieldFrom(argList.get(i), sFields);
						}
					}
					
				}
				
				if (citem.getInterfName().equals(this.notAnInterface) || citem.getInterfName().equals(this.MultiThrdInvoke)) {	// Normal return, return to caller site.
					this.sContext.setMethodLocation(citem.getSmethd());
					this.sContext.setBlockLocation(citem.getBlcok());
					this.sContext.setInstructionLocation(citem.getCurrentInstruction(), true);
					this.sContext.setParam2Var(citem.getParam2Var());

					this.sContext.taintedParams = new HashMap<Integer, HashSet<String>>();	// Reset the tainted Params
				} else {	// Jump into next interface invoke, or return to caller site
					
//					if (interestinRet && citem.getReturnTarget() != null){	// add interested in return target
//						this.sContext.addIntrestedVariable(citem.getReturnTarget(), this.sContext.getIntrestedVariable().get(citem.getReturnTarget()));
//						
//					}
					
					if (!citem.isFirstInterf())	{	// if jump into next interface invoke, add interested pref
						this.sContext.addAllIntrestedVariable(citem.getInterestedPref());
						this.sContext.setParam2Var(new ArrayList<>());	//	function invocation, must be instance invoke
						this.sContext.invokeLayer++;
						this.sContext.resetCashedAssignStmt();	// Start at a new interface method, reset cashedAssign
					} else { // Similar to normal return, return to the caller site
						this.sContext.setParam2Var(citem.getParam2Var());
						this.sContext.taintedParams = new HashMap<Integer, HashSet<String>>();	// Reset the tainted Params
					}
					
					this.sContext.setMethodLocation(citem.getSmethd());
					this.sContext.setBlockLocation(citem.getBlcok());
					this.sContext.setInstructionLocation(citem.getCurrentInstruction(), true);
					
//					System.out.println("Switch to " + this.sContext.getMethodLocation());
//					pauseWhile();
				}
			}
		}
	}
	
	
	public void trackMultiThrdTaint(Value ri) {
		int depth = 0;
		SootMethod targetMthd = this.sContext.getMethodLocation();
		while (depth < 5 && ri != null) {
//			System.out.println("Now ri=" + ri);
			depth++;
			Value rop = null;
			boolean Found = false;
			if (ri instanceof StaticFieldRef) {
				String iField = ((FieldRef)ri).getField().toString();
//				System.out.println(varName);
				for (SootClass sclas : Scene.v().getClasses()) {
					if (Found) break;
					for (SootMethod smthd : ListUtility.clone(sclas.getMethods())) {
						if (Found) break;
						if (!smthd.isConcrete())
							continue;
	
						Body body = smthd.retrieveActiveBody();
						if (body == null)
							continue;
						
	
						List<Block> bs = BlockGenerator.getInstance().generate(body).getBlocks();
	
						for (Block block : bs) {
							if (Found) break;
							for (Unit unit : block) {
								if (unit instanceof AssignStmt) {
									Value lop = ((AssignStmt) unit).getLeftOp();
									if (!(lop instanceof FieldRef)) continue;
									if (((FieldRef)lop).getField().toString().equals(iField)) {
										rop = ((AssignStmt) unit).getRightOp();
										targetMthd = smthd;
										Found = true;
										break;
									}
								}
							}
						}
					}
				}
			} else if (ri instanceof InstanceFieldRef) {	// is a field ref
				String iField = ((FieldRef)ri).getField().toString();
//				System.out.println(varName);
//				for (SootClass sclas : Scene.v().getClasses()) {
				SootClass sclas = Scene.v().getSootClass(ListUtility.getSubString("<", ":", iField));
				if (Found) break;
				for (SootMethod smthd : ListUtility.clone(sclas.getMethods())) {
					if (Found) break;
					if (!smthd.isConcrete())
						continue;

					Body body = smthd.retrieveActiveBody();
					if (body == null)
						continue;
					

					List<Block> bs = BlockGenerator.getInstance().generate(body).getBlocks();

					for (Block block : bs) {
						if (Found) break;
						for (Unit unit : block) {
							if (unit instanceof AssignStmt) {
								Value lop = ((AssignStmt) unit).getLeftOp();
								if (!(lop instanceof FieldRef)) continue;
								if (((FieldRef)lop).getField().toString().equals(iField)) {
									rop = ((AssignStmt) unit).getRightOp();
									targetMthd = smthd;
									Found = true;
									break;
								}
							}
						}
					}
				}
//				}
			} else if (ri instanceof ParameterRef) {	//	From function invocation
//				int paraIndex = Integer.parseInt(ListUtility.getSubString("@parameter", ":", ri.toString()));
				int paraIndex = ((ParameterRef) ri).getIndex();
				String targetMthdSig = targetMthd.getSignature();
//				System.out.println(ri.toString() + " " + paraIndex + ", TargetMthd: " + targetMthdSig);
				
				for (SootClass sclas : Scene.v().getClasses()) {
					if (Found) break;
					
					for (SootMethod smthd : ListUtility.clone(sclas.getMethods())) {
//						if (smthd.toString().contains("de.ecspride"))System.out.println("++++++NOW inside method:" + smthd);
						if (Found) break;
						if (!smthd.isConcrete())
							continue;

						Body body = smthd.retrieveActiveBody();
						if (body == null)
							continue;
						

						List<Block> bs = BlockGenerator.getInstance().generate(body).getBlocks();

						for (Block block : bs) {
							if (Found) break;
							for (Unit unit : block) {
								InvokeExpr invoke = null;
								
								if (unit instanceof AssignStmt && ((AssignStmt) unit).getRightOp() instanceof InvokeExpr) 
									invoke = (InvokeExpr)((AssignStmt) unit).getRightOp();
								if (unit instanceof InvokeStmt)
									invoke = ((InvokeStmt) unit).getInvokeExpr();
								if (invoke == null) continue;
//								System.out.println("Invoke Signature: " + invoke.getMethodRef().getSignature());
								if (invoke.getMethodRef().getSignature().equals(targetMthdSig)){
//									System.out.println("Found target Mthd: " + unit);
									rop = invoke.getArgs().get(paraIndex);
									Found = true;
									targetMthd = smthd;
									break;
								}
								
							}
						}
					}
				}
				
			} else {	//	Assignment
//				System.out.println("****Is assignment: " + targetMthd.toString());
				Body body = targetMthd.retrieveActiveBody();
				if (body == null){
					System.out.println("Error in finding multithread function...");
					break;
				}
					

				List<Block> bs = BlockGenerator.getInstance().generate(body).getBlocks();

				for (Block block : bs) {
					if (Found) break;
					for (Unit unit : block) {
//						System.out.println(unit + ", is identity? " + (unit instanceof IdentityStmt));
						if (unit instanceof AssignStmt) {
//							System.out.println(unit + ": " + ((AssignStmt) unit).getLeftOp() + " equals " + ri.toString() + " ? " + ((AssignStmt) unit).getLeftOp().equals(ri));
							if (((AssignStmt) unit).getLeftOp().equals(ri)) {
								rop = ((AssignStmt) unit).getRightOp();
								Found = true;
								break;
							}
						} else if (unit instanceof IdentityStmt) {
							if (((IdentityStmt) unit).getLeftOp().equals(ri)) {
								rop = ((IdentityStmt) unit).getRightOp();
								Found = true;
								break;
							}
						}
					}
				}
				
			}
			if (rop != null && rop instanceof NewExpr) {
				InvokeMultiThrdFunction(rop);
				break;
			} else ri = rop;
		}
	}
	
	public boolean isMultiThrdInvoke(Value r) {
//		System.out.println(r.toString());
		if (r instanceof NewExpr){
//			System.out.println(r.toString() + " Newexpr");
			return true;
		}
		return false;
	}
	
	public void InvokeMultiThrdFunction(Value r) {	// r is a NewExpr
		boolean isFirst = true;
		CallStackItem citem = null;
		SootClass scls = Scene.v().getSootClass(((NewExpr)r).getBaseType().toString()).getSuperclass();
		SootMethod targetMthd = null;
		HashSet<String> sField = new HashSet<>();
		HashSet<String> interfSet = new HashSet<>();
		
		for (SootClass Interf : scls.getInterfaces()) {
			interfSet.add(Interf.toString());
		}
		
		// For interface func, need to find the implementation from the current class to the parent class
		if (currentMultiThrdFunc.getMethod().toString().contains("(java.lang.Runnable")) {	
			String mthdName = "run";	// For Runnable -> run()
			SootClass curClass = Scene.v().getSootClass(((NewExpr)r).getBaseType().toString());
			while (!curClass.declaresMethodByName(mthdName) && curClass.hasSuperclass()) {
				curClass = curClass.getSuperclass();
				if (curClass.toString().equals("java.lang.Object")) break;
			}
			if (curClass.toString().equals("java.lang.Object")) return;
			if (curClass.declaresMethodByName(mthdName)) {
				targetMthd = curClass.getMethodByName(mthdName);
				jump2Mthd(targetMthd, true);
			}
			return;
		}
		
		
		
		// For abstract class
		while (!(runTest.intrestedSuperClass.contains(scls.toString()) || scls.toString().equals("java.lang.Object")))
			scls = scls.getSuperclass();
		if (scls.toString().equals("java.lang.Object")) return;
		switch (scls.toString()){
			case "android.os.Handler":
				targetMthd = Scene.v().getSootClass(((NewExpr)r).getBaseType().toString()).getMethodByName("handleMessage");
				sField.add("<android.os.Message: java.lang.Object obj>");
				jump2Mthd(targetMthd, true);
//				System.out.println("Selected targetMthd: " + targetMthd.toString());
				return;
			case "android.os.AsyncTask":
				targetMthd = Scene.v().getSootClass(((NewExpr)r).getBaseType().toString()).getMethod("java.lang.Object doInBackground(java.lang.Object[])");
				jump2Mthd(targetMthd, true);
//				System.out.println("Selected targetMthd: " + targetMthd.toString());
				return;
		}
	}
	
	public HashSet<String> diffWithField(HashSet<String> totalField, String fieldToRemove) {
		HashSet<String> sField = new HashSet<>();
		
		HashSet<SootClass> toCheckSubClassSet = new HashSet<>();
		String tempString = ListUtility.getSubString(": ", ">", fieldToRemove);
		SootClass baseClass = Scene.v().getSootClass(ListUtility.getSubString("", " ", tempString));
		toCheckSubClassSet.add(baseClass);
		
		int fieldSize = 0;
		
		boolean changed = true;
		
		while (toCheckSubClassSet.size() > 0 && changed) {
			baseClass = toCheckSubClassSet.iterator().next();

			if (baseClass.isApplicationClass())
				for (SootField sf : baseClass.getFields()) {
					if (totalField.contains(sf.toString())){
						sField.add(sf.toString());
						tempString = ListUtility.getSubString(": ", ">", sf.toString());
						toCheckSubClassSet.add(Scene.v().getSootClass(ListUtility.getSubString("", " ", tempString)));
					}
				}
			toCheckSubClassSet.remove(baseClass);
		}
		return sField;
	}

	public Value getBaseValue(Value r) {
		if (r instanceof ArrayRef) return ((ArrayRef) r).getBase();
		if (r instanceof InstanceFieldRef) {
			return ((InstanceFieldRef) r).getBase();
			
		}
		if (r instanceof CastExpr) return getBaseValue(((CastExpr) r).getOp());
		
		if (r instanceof InstanceInvokeExpr) return ((InstanceInvokeExpr)r).getBase();
		return r;
	}

	
	public Value getValue(Value r) {
		if (r instanceof ArrayRef) return ((ArrayRef) r).getBase();
		if (r instanceof CastExpr) return ((CastExpr) r).getOp();
		return r;
	}
	
	public void propagateTaintFieldFrom(Value var, HashSet<String> inFields) {
		
		HashSet<String> sFields = inFields == null ? new HashSet<>() : (HashSet<String>) inFields.clone();
		if (var instanceof InstanceFieldRef)
			sFields.addAll(TaintQuestionSolver.getFieldsInChildClass(((InstanceFieldRef) var).getField().toString()));
		
		if (var instanceof StaticFieldRef) {	// Directly add the static Field is OK.
			FieldRef fieldRef = (StaticFieldRef) var;
			if (!TaintQuestionSolver.staticFieldVariableSet.contains(fieldRef.getField().toString()))
				TaintQuestionSolver.newStaticFieldSet.add(fieldRef.getField().toString());
			return;
		}
		
		
		int i = this.sContext.cashedAssgnStmt.size() - 2;
		if (i < 0) {	//	Normal assignment
			this.sContext.addIntrestedVariable(getBaseValue(var), sFields);
			return;
		}
		
		DefinitionStmt curAssign = this.sContext.getCashedAssignStmt().get(i);
		Value pValue = getValue(curAssign.getRightOp());
		Value pBase = getBaseValue(pValue);
		Value medValue = curAssign.getLeftOp();
		
		if (!(pValue instanceof FieldRef)) {	// No need to propagate
			this.sContext.addIntrestedVariable(getBaseValue(var), sFields);
			return;
		}
		

		
		// Below is for InstanceRef
		
		Value curValue = var;
		Value curBase = getBaseValue(curValue);
		
		//	Taint successors' fields
		this.sContext.addIntrestedVariable(curBase, sFields);
		
		
		
		while (i >= 0 && curBase.equals(medValue)) {	// Ensure the propagation relation
			curValue = getValue(curAssign.getRightOp());
			curBase = getBaseValue(curValue);
			if (!(curValue instanceof InstanceFieldRef)) break;
			sFields.addAll(TaintQuestionSolver.getFieldsInChildClass(((InstanceFieldRef)curValue).getField().toString()));
			this.sContext.addIntrestedVariable(curBase, sFields);
			i--;
			if (i >= 0) curAssign = this.sContext.getCashedAssignStmt().get(i);
			else break;
			medValue = getValue(curAssign.getLeftOp());
		}
		
			
	}
	
	public void sequentialRemoveFieldFrom(Value var) {
		if (!this.sContext.getIntrestedVariable().containsKey(var))
			return;
		HashSet<String> sFields = new HashSet<>();
		if (var instanceof InstanceFieldRef)
			sFields.addAll(TaintQuestionSolver.getFieldsInChildClass(((InstanceFieldRef) var).getField().toString()));
		
		int i = this.sContext.cashedAssgnStmt.size() - 2;
		if (i < 0) {	//	Normal assignment
			this.sContext.removeIntrestedVariable(getBaseValue(var), sFields);
			return;
		}
		
		DefinitionStmt curAssign = this.sContext.getCashedAssignStmt().get(i);
		Value pValue = curAssign.getRightOp();
		Value pBase = getValue(pValue);
		

		if (!(pValue instanceof FieldRef)) {	// No need to propagate
			this.sContext.removeIntrestedVariable(getBaseValue(var), sFields);
			return;
		}
		
		if (var instanceof StaticFieldRef) {	// Directly add the static Field is OK.
			FieldRef fieldRef = (StaticFieldRef) var;
			TaintQuestionSolver.newStaticFieldSet.remove(fieldRef.getField().toString());
			return;
		}
		
		
		Value curValue = var;
		Value curBase = getBaseValue(curValue);
		
//		remove all successor's tainted fields
		this.sContext.removeIntrestedVariable(curBase, sFields);
		
		if (sFields.isEmpty()) return;
		Value medValue = curAssign.getLeftOp();
		
		while (i >= 0 && curBase.equals(medValue)) {	// Ensure the propagation relation
//			System.out.println(curBase + " " + medValue);
//			System.out.println("curAssign: " + curAssign);
			curValue = getValue(curAssign.getRightOp());
			curBase = getBaseValue(curValue);
			if (!(curValue instanceof InstanceFieldRef)) break;
			
			this.sContext.removeIntrestedVariable(curBase, sFields);
//			System.out.println("remove " + sFields + " from " + curBase + " , After: " + this.sContext.getIntrestedVariable().get(curBase));
			i--;
			if (i >= 0) curAssign = this.sContext.getCashedAssignStmt().get(i);
			else break;
			medValue = getBaseValue(curAssign.getLeftOp());
		}
		
	}
	
	public void getTaintedParamAtStart() {	//	Set the tainted param at the first layer
//		System.out.println("++++++Enter the tainted param start func\n++++++Current tainted Params: " + this.sContext.getTaintedParams());
		HashMap<Value, HashSet<String>> tMap = (HashMap<Value, HashSet<String>>) this.sContext.getIntrestedVariable().clone();
		SootMethod targetMthd = this.sContext.getMethodLocation();
		ArrayList<DefinitionStmt> defList = new ArrayList<>();
		
		
		Body body = targetMthd.retrieveActiveBody();
		List<Block> bs = BlockGenerator.getInstance().generate(body).getBlocks();
		List<Type> prefTypeList = this.sContext.getMethodLocation().getParameterTypes();
		
		for (Unit unit : bs.get(0)) {
			if (unit instanceof IdentityStmt) {
				IdentityStmt stmt = (IdentityStmt) unit;
				Value rop = stmt.getRightOp();
				Value lop = stmt.getLeftOp();
				
				if (rop instanceof ParameterRef && this.sContext.getIntrestedVariable().containsKey(lop)) {
					int paramIndex = Integer.parseInt(ListUtility.getSubString("@parameter", ":", rop.toString()));
					if (!runTest.ImmutableClass.contains(prefTypeList.get(paramIndex).toString())) {
						this.sContext.getTaintedParams().put(paramIndex, this.sContext.getIntrestedVariable().get(lop));
					} 
//					else System.out.println("Not adding " + prefTypeList.get(paramIndex).toString() + ", since immutable");
				} else if (rop instanceof ThisRef && this.sContext.getIntrestedVariable().containsKey(lop)) {
					this.sContext.getTaintedParams().put(-1,this.sContext.getIntrestedVariable().get(lop));
				}
			} else break;
		}		
	}
	
	
	public String getHardCodedKey(Value v) {	// Find a StringConstant
		int paraIndex = 0;
		String targetMthdSig = null;
		boolean findingMthd = false;
		int idx = this.sContext.getInstructionTrace().size() - 1;
		while (idx > 0) {
//			System.out.println("current v: " + v.toString());
			
			if (v instanceof StringConstant) 
				return ((StringConstant)v).value;
			idx--;
			StmtItem item = this.sContext.getInstructionTrace().get(idx);
			
			Unit curInstruction = item.getU();
//			System.out.println("current inst: " + curInstruction.toString());
			if (findingMthd) {
				if (curInstruction instanceof AssignStmt)
					if (((AssignStmt) curInstruction).getRightOp() instanceof InvokeExpr 
							&& ((InvokeExpr)((AssignStmt) curInstruction).getRightOp()).getMethod().getSignature().equals(targetMthdSig)) {
						v = ((InvokeExpr)((AssignStmt) curInstruction).getRightOp()).getArg(paraIndex);
						findingMthd = false;
					}
				if (curInstruction instanceof InvokeStmt
						&& ((InvokeStmt) curInstruction).getInvokeExpr().getMethod().getSignature().equals(targetMthdSig)) {
//					System.out.println("cur invoke: " + ((InvokeStmt) curInstruction).getInvokeExpr().getMethod().getSignature());
					v = ((InvokeStmt) curInstruction).getInvokeExpr().getArg(paraIndex);
					findingMthd = false;
				}
				continue;
			}
			if (curInstruction instanceof DefinitionStmt) {
				Value lop = ((DefinitionStmt) curInstruction).getLeftOp();
				Value rop = ((DefinitionStmt) curInstruction).getRightOp();
				if (lop != v) continue;
				v = rop;
				if (v instanceof ParameterRef) {
					paraIndex = ((ParameterRef) v).getIndex();
					targetMthdSig = item.getSm().getSignature();
//					System.out.println("TargetMthd: " + targetMthdSig);
					findingMthd = true;
				}
			}
		}
		
		return "";
	}
	
}