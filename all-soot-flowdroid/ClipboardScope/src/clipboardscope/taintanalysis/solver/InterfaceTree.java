package clipboardscope.taintanalysis.solver;

import java.util.ArrayList;
import java.util.HashMap;

import soot.SootMethod;
import soot.Value;

public class InterfaceTree {
	TreeNode root = null;
	TreeNode curNode = null;
	ArrayList<TreeNode> curTrace = null;
	int curLayer;
	boolean isComplete;
	HashMap<Value, TreeNode> value2Node; 	//Map the current interface invoke to the target TreeNode
//	int maxDepth = 2;
	
	public InterfaceTree(SootMethod smthd){
		this.root = new TreeNode(0, smthd);
		curNode = root;
		curLayer = 0;
		isComplete = false;
		curTrace = new ArrayList<TreeNode>();
		curTrace.add(root);
		value2Node = new HashMap<Value, TreeNode>();
	}
	
	public TreeNode getCurNode() {
		return curNode;
	}
	
	public void completeOneTrace() {
		TreeNode tmpNode = curNode;
		curNode = curNode.getNextSibling();
		curTrace.remove(curTrace.size() - 1);
		while (curNode == null) {	// check whether it is the last children
			curNode = tmpNode.getParent();
			if (curNode == null) {	// At root
				isComplete = true;
				break;
			}
			curTrace.remove(curTrace.size() - 1);
			if (curTrace.size() == 0)
				System.out.println("Empty trace");
			tmpNode = curNode;
			curNode = curNode.getNextSibling();
		}
		curTrace.add(curNode);
		if (!isComplete){
			printTrace();
		}
		curNode = root;	//reset the curNode position
		curLayer = 0;
	}
	
	public void printTrace() {
		System.out.print("Cur Trace :[");
		for (TreeNode treeNode : curTrace) 
			System.out.print(treeNode.getSootMethod().toString() + ", ");
		System.out.println("]");
	}
	
	public int oneStepForward() {
		++curLayer;
		if (curLayer >= curTrace.size())
			curTrace.add(curNode.getChildren().get(0));	// For new added children, should check whether is leaf first. If yes, do add child first.
//		System.out.println("Trace: " + curTrace.toString());
		curNode = curTrace.get(curLayer);
		return curNode.getId();
	}
	
	public void addOneChild(int id, SootMethod smthd) {
//		if (curTrace.size() >= maxDepth) return;
		if (curNode.isLeaf()) {
//			if (curLayer == 0)
//				if (!smthd.toString().equals("<com.taobao.tao.flexbox.layoutmanager.ac.f$2: void a(com.taobao.tao.flexbox.layoutmanager.ac.f$c,java.lang.Object)>"))
//					return;
			curNode.addChild(new TreeNode(id, smthd));
		}
		else {
//			if (curLayer == 0)
//				if (!smthd.toString().equals("<com.taobao.tao.flexbox.layoutmanager.ac.f$2: void a(com.taobao.tao.flexbox.layoutmanager.ac.f$c,java.lang.Object)>"))
//					return;
			TreeNode lastChild = curNode.getChildren().get(curNode.getChildren().size() - 1);
			TreeNode newNode = new TreeNode(id, smthd);
			lastChild.setNextSibling(newNode);
			curNode.addChild(newNode);
			
		}
	}

	
}
