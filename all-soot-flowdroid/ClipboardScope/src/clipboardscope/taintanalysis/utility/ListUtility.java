package clipboardscope.taintanalysis.utility;

import java.util.ArrayList;
import java.util.List;

import soot.PatchingChain;
import soot.Unit;

public class ListUtility {

	public static List<Unit> chain2List(PatchingChain<Unit> us) {
		List<Unit> ls = new ArrayList<Unit>();
		for (Unit inst : us) {
			ls.add(inst);
		}
		return ls;
	}

	public static <T> List<T> Array2List(T[] ts) {
		List<T> ls = new ArrayList<T>();
		for (T inst : ts) {
			ls.add(inst);
		}
		return ls;
	}

	public static <T> List<T> clone(List<T> ls) {
		List<T> list = new ArrayList<T>();
		for (T t : ls) {
			list.add(t);
		}
		return list;
	}
	
	public static String getSubString(String startStr, String endStr, String paraName) {
        int strStartIndex = paraName.indexOf(startStr);
        int strEndIndex = paraName.indexOf(endStr);
 
        if (strStartIndex < 0) {
            return "error to get class name for:" + paraName;
        }
        if (strEndIndex < 0) {
        	return "error to get class name for:" + paraName;
        }
//        System.out.println(paraName + " " + strStartIndex + " " + strEndIndex);
        strStartIndex += startStr.length();
        if (strEndIndex < strStartIndex) return "error to get class name for:" + paraName;
        String result = paraName.substring(strStartIndex, strEndIndex);
        
		return result;
	}
}
