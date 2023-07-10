package clipboardscope.taintanalysis.utility;

import java.util.concurrent.atomic.AtomicBoolean;

import clipboardscope.main.runTest;
import clipboardscope.taintanalysis.main.QuestionGenerator;
import clipboardscope.taintanalysis.solver.TaintQuestionSolver;

public class TimeUtility {

	public static void main(String[] args) {
		// TODO Auto-generated method stub

	}

	
	public static void startWatcherBruce(int sec) {
		Thread t = new Thread() {
			public void run() {
				try {
					Thread.sleep(sec * 1000);
				} catch (InterruptedException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
				Logger.printE("TimeOut");

				String line = String.format("%s | %s | %s | %s", 0, "timeout", runTest.pn, "");

				FileUtility.wf("TimeOuts.txt", line, true);
				runTest.saveInitResult();
				System.exit(0);
				runTest.timeout = true;
				runTest.questionTimeout = true;
			}
		};
		t.setDaemon(true);
		t.start();
	}
	
	public static Thread startWatcherOneQuestionBruce(int sec) {
		Thread t = new Thread() {
			private AtomicBoolean timeout = new AtomicBoolean(true);
		    
//			public void interrupt() {
//		        running.set(false);
//		        this.interrupt();
//		    }
		    
			public void run() {
//				running.set(true);
				try {
					Thread.sleep(sec * 1000);
				} catch (InterruptedException e) {
					// TODO Auto-generated catch block
//					e.printStackTrace();
					timeout.set(false);
					Thread.currentThread().interrupt();
				}
				Logger.printE("TimeOut one question");

//				System.exit(0);
				if (timeout.get()) runTest.questionTimeout = true;
			}
			
			
		};
		t.setDaemon(true);
		t.start();
		return t;
	}
}
