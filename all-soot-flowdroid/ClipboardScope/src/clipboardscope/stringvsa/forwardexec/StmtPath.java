package clipboardscope.stringvsa.forwardexec;

import java.util.List;

import clipboardscope.stringvsa.base.StmtPoint;
import soot.Unit;

public interface StmtPath {

	public Unit getStmtPathHeader();

	public Unit getSuccsinStmtPath(Unit u);

	public Unit getPredsinStmtPath(Unit u);

	public Unit getStmtPathTail();

	public List<StmtPoint> getStmtPath();
}
