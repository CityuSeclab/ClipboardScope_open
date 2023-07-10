package clipboardscope.taintanalysis.solver;

import java.util.ArrayList;

import soot.SootMethod;

class TreeNode{
	int id;
	ArrayList<TreeNode> children = null;
	TreeNode parent = null;
	TreeNode nextSibling = null;
	SootMethod sootMethod = null;
	
	public TreeNode(int n) {
		setId(n);
		nextSibling = null;
	}
	
	public TreeNode(int n, SootMethod smthd) {
		setId(n);
		nextSibling = null;
		this.sootMethod = smthd;
	}
	
	public void setNextSibling(TreeNode sb) {
		this.nextSibling = sb;
	}
	
	public void setId(int n) {
		this.id = n;
	}
	
	public void setParent(TreeNode c) {
		this.parent = c;
	}
	
	public boolean isLeaf() {
		return children == null ? true : false;
	}
	
	public void addChild(TreeNode c) {
		if (children == null) children = new ArrayList<TreeNode>();
		c.setParent(this);
		children.add(c);
	}
	
	public ArrayList<TreeNode> getChildren(){
		return this.children;
	}
	
	public int getId(){
		return this.id;
	}
	
	public TreeNode getParent(){
		return this.parent;
	}
	
	public int getSiblingNum(){
		return this.parent == null ? 0 : this.parent.getChildren().size();
	}
	
	public TreeNode getNextSibling() {
		return this.nextSibling;
	}
	
	public SootMethod getSootMethod() {
		return this.sootMethod;
	}
}