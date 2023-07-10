package clipboardscope.taintanalysis.solver;

import java.util.ArrayList;

import soot.SootMethod;

public class RootNode {	//Root node for an interface invoke
	int curPos;	// processing which child
	ArrayList<SootMethod> childrenList;
	int childrenNum;
	String signature;	//interface name + method template
	
	public RootNode(String sig) {
		// TODO Auto-generated constructor stub
		childrenList = new ArrayList<SootMethod>();
		childrenNum = 0;
		curPos = 0;
		signature = sig;
	}
	
	public void addOneMethod(SootMethod m) {
		childrenList.add(m);
		childrenNum++;
	}
	
	public SootMethod getNextMthd() {
		return curPos < childrenNum ? childrenList.get(curPos++) : null;
	}
	
	public SootMethod getCurMthd() {
		return curPos < childrenNum ? childrenList.get(curPos) : null;
	}
	
	
	
}
