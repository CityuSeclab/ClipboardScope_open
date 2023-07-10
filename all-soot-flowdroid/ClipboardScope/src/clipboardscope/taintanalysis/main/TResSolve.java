package clipboardscope.taintanalysis.main;

import java.util.ArrayList;
import java.util.Enumeration;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.List;

import org.json.JSONObject;

import clipboardscope.main.runTest;
import clipboardscope.taintanalysis.base.TaintQuestion;
import clipboardscope.taintanalysis.solver.SimulationContext;
import clipboardscope.taintanalysis.solver.StmtItem;
import clipboardscope.taintanalysis.utility.FileUtility;
import clipboardscope.taintanalysis.utility.MethodUtility;

public class TResSolve {

	@SuppressWarnings("unchecked")
	public static HashSet<String> saveSolved(List<TaintQuestion> solved) {

		HashSet<String> svd = new HashSet<String>();
		ArrayList<StmtItem> stmts;
		String tmp;
		for (TaintQuestion tq : solved) {

			JSONObject source = new JSONObject();
			source.put("method", tq.getSourcep().getMethodLocation().toString());
			source.put("unit", tq.getSourcep().getInstructionLocation().toString());
			source.put("unitIndex", MethodUtility.getUnitIndex(tq.getSourcep().getMethodLocation(), tq.getSourcep().getInstructionLocation()));

			for (SimulationContext sc : tq.getsContexts()) {
				if (sc.isContainsSink()) {

					JSONObject ret = new JSONObject();
					ret.put("package", runTest.pn);
					ret.put("source", source);

					stmts = (ArrayList<StmtItem>) sc.getInstructionTrace().clone();
					for (StmtItem stmt : stmts)
						if (stmt.isContainsSink()) {

							JSONObject sink = new JSONObject();
							sink.put("method", stmt.getSm().toString());
							sink.put("unit", stmt.getU());
							sink.put("unitIndex", MethodUtility.getUnitIndex(stmt.getSm(), stmt.getU()));
							
							if (stmt.getCurIntst() != null)
								sink.put("taint_var", stmt.getCurIntst());
							ret.append("sinks", sink);

						}
					tmp = ret.toString();
					if (!svd.contains(tmp)) {
						svd.add(tmp);
//						FileUtility.wf("taintResTmp.txt", tmp, true);
					}
				}
			}
		}
		return svd;
		
	}
	
	public static HashSet<String> saveSolved(Hashtable<Integer, ArrayList<TaintQuestion>> solvedList) {

		HashSet<String> svd = new HashSet<String>();
		ArrayList<StmtItem> stmts;
		String tmp;
		
		Enumeration<Integer> e = solvedList.keys();
		while (e.hasMoreElements()){
			int key = e.nextElement();
			ArrayList<TaintQuestion> solvedOneTq = solvedList.get(key);
			for (TaintQuestion tq : solvedOneTq) {
	
				JSONObject source = new JSONObject();
				source.put("method", tq.getSourcep().getMethodLocation().toString());
				source.put("unit", tq.getSourcep().getInstructionLocation().toString());
				source.put("unitIndex", MethodUtility.getUnitIndex(tq.getSourcep().getMethodLocation(), tq.getSourcep().getInstructionLocation()));
				source.put("RC", tq.getRC());
	
				JSONObject Orisource = new JSONObject();
				Orisource.put("method", tq.getOriSourcep().getMethodLocation().toString());
				Orisource.put("unit", tq.getOriSourcep().getInstructionLocation().toString());
				Orisource.put("unitIndex", MethodUtility.getUnitIndex(tq.getOriSourcep().getMethodLocation(), tq.getOriSourcep().getInstructionLocation()));

				
				for (SimulationContext sc : tq.getsContexts()) {
					if (sc.isContainsSink()) {
	
						JSONObject ret = new JSONObject();
						ret.put("package", runTest.pn);
						ret.put("source", source);
						ret.put("iniPoint", Orisource);
	
						stmts = (ArrayList<StmtItem>) sc.getInstructionTrace().clone();
						for (StmtItem stmt : stmts)
							if (stmt.isContainsSink()) {
	
								JSONObject sink = new JSONObject();
								sink.put("method", stmt.getSm().toString());
								sink.put("unit", stmt.getU());
								sink.put("unitIndex", MethodUtility.getUnitIndex(stmt.getSm(), stmt.getU()));
								
								if (stmt.getCurIntst() != null)
									sink.put("taint_var", stmt.getCurIntst().toString());
								ret.append("sinks", sink);
	
							}
						tmp = ret.toString();
						if (!svd.contains(tmp)) {
							svd.add(tmp);
//							FileUtility.wf("taintResTmp.txt", tmp, true);
						}
					}
				}
			}
		}
		return svd;
		
	}

}
