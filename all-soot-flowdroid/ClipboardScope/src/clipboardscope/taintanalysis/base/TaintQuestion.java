package clipboardscope.taintanalysis.base;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

import org.jf.smali.smaliParser.debug_directive_return;

import clipboardscope.taintanalysis.solver.SimulationContext;
import clipboardscope.taintanalysis.solver.TaintQuestionSolver;
import clipboardscope.taintanalysis.utility.ListUtility;
import soot.Scene;
import soot.SootMethod;

public class TaintQuestion {
	SourcePoint sourcep;
	SourcePoint originp;
	List<SinkMethod> sinks;
	boolean isInitialSource;
	List<SimulationContext> sContexts = new ArrayList<>();
	boolean reconnect_control = false;
	
	
	public TaintQuestion(SourcePoint sourcep, boolean isInitial, SourcePoint originp) {
		setSourcep(sourcep);
		sinks = new ArrayList<>();
		isInitialSource = isInitial;
		
		if (isInitialSource) this.originp = sourcep;
		else this.originp = originp;
		
		SimulationContext sc = new SimulationContext(sourcep.getMethodLocation(), sourcep.getBlockLocation(), sourcep.getInstructionLocation());
		HashSet<String> set = new HashSet<>();
		if (sourcep.getTartgetField() != null) set.addAll(sourcep.getTartgetField());
		sc.addIntrestedVariable(sourcep.getTartgetValue(), set);
		sContexts.add(sc);

	}
	
	public TaintQuestion(SourcePoint sourcep, boolean isInitial, SourcePoint originp, boolean reconnect) {
		setSourcep(sourcep);
		sinks = new ArrayList<>();
		isInitialSource = isInitial;
		
		if (isInitialSource) this.originp = sourcep;
		else this.originp = originp;
		
		SimulationContext sc = new SimulationContext(sourcep.getMethodLocation(), sourcep.getBlockLocation(), sourcep.getInstructionLocation());
		HashSet<String> set = new HashSet<>();
		if (sourcep.getTartgetField() != null) set.addAll(sourcep.getTartgetField());
		sc.addIntrestedVariable(sourcep.getTartgetValue(), set);
		sContexts.add(sc);
		this.reconnect_control = reconnect;
	}
	
	public boolean getRC() {
		return reconnect_control;
	}

	public SourcePoint getSourcep() {
		return sourcep;
	}
	
	public SourcePoint getOriSourcep() {
		return originp;
	}

	public void setSourcep(SourcePoint sourcep) {
		this.sourcep = sourcep;
	}

	public List<SinkMethod> getSinks() {
		return sinks;
	}

	public void addSinks(SinkMethod sink) {
		this.sinks.add(sink);
	}

	public List<SimulationContext> getsContexts() {
		return sContexts;
	}

	public void addSContexts(SimulationContext sContext) {
		if (!sContexts.contains(sContext))
			this.sContexts.add(sContext);
	}

	public boolean isSink(SootMethod sm) {

		for (SinkMethod sinkm : sinks) {
			if (sinkm.getMethodLocation().equals(sm))
				return true;
		}
		if (sm.getSignature().contains("setText")
				|| sm.getSignature().contains("setHint")
				|| (sm.getSignature().contains("<java.io.") && sm.getSignature().contains("void print"))
				|| sm.getSignature().contains("android.widget.Toast")
				|| (sm.getSignature().contains("<java.io.") && sm.getSignature().contains("void write"))
				|| sm.getSignature().contains("isEmpty(")
				|| (sm.getSignature().contains("<android.content.Intent") && sm.getSignature().contains("putExtra"))
				|| (sm.getSignature().contains("<android.database.sqlite.SQLiteDatabase") && sm.getSignature().contains("insert"))
				|| (sm.getSignature().contains("<android.database.sqlite.SQLiteDatabase") && sm.getSignature().contains("exec"))
				|| sm.getSignature().contains(" setEntity(") //
				|| sm.getSignature().contains("java.net") && sm.getSignature().contains("getOutputStream()")
				) return true;
		return false;

	}

	public boolean isPositive() {
		for (SimulationContext sContext : sContexts) {
			if(sContext.isContainsSink())
				return true;
		}
		return false;
	}
}



