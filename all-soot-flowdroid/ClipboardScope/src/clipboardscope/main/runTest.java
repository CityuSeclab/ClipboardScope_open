package clipboardscope.main;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.List;
import java.util.Set;

import org.jf.dexlib2.immutable.ImmutableClassDef;
import org.jf.smali.SmaliMethodParameter;
import org.json.JSONArray;
import org.json.JSONObject;

import clipboardscope.stringvsa.backwardslicing.TaintRules;
import clipboardscope.stringvsa.graph.CallGraph;
import clipboardscope.stringvsa.graph.DGraph;
import clipboardscope.stringvsa.graph.IDGNode;
import clipboardscope.stringvsa.graph.ValuePoint;
import clipboardscope.stringvsa.utility.Logger;
import clipboardscope.taintanalysis.base.TaintQuestion;
import clipboardscope.taintanalysis.main.QuestionGenerator;
import clipboardscope.taintanalysis.solver.InterfaceTree;
import clipboardscope.taintanalysis.utility.FileUtility;
import clipboardscope.taintanalysis.utility.TimeUtility;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Value;
import soot.asm.backend.targets.nullTypes;
import soot.jimple.AssignStmt;
import soot.options.Options;

public class runTest {
	public static String path;
	public static String pn;
	static Hashtable<String, Hashtable<String, String>> m2m;
	
	public static Hashtable<String, HashSet<String>> interfMthdTplt;
	public static Hashtable<String, ArrayList<SootMethod>> i2c;
	public static HashMap<String, HashSet<Value>> globalVar2MultiThrdCls;
	public static HashMap<SootClass, HashSet<SootClass>> childrenTable;
	public static ArrayList<String> sinkMetds = new ArrayList<String>();
	public static ArrayList<String> vsaMetds = new ArrayList<String>();
	public static HashMap<String, HashSet<Integer>> inputMetds2TaintedVar = new HashMap<String, HashSet<Integer>>(); 
	public static ArrayList<String> inputMetds = new ArrayList<String>();
	public static QuestionGenerator qg = null;
	public static HashSet<String> ImmutableClass = new HashSet<String>();
	public static HashSet<String> intrestedSuperClass = new HashSet<String>();
	
	public static HashSet<String> searchedKeys = new HashSet<>();
	
	public static boolean questionTimeout = false;
	public static boolean timeout = false;
	public static HashSet<String> init_taint_res = null;
	
	// args[0] app package name
	// args[1] android.jar path
	public static void main(String[] args) {
		
		System.out.println("app: " + args[0] + ", android_jar: " + args[1]);
		
		String fp = "";
		fp = args[0];

//		String ajar = "android.jar";
		String ajar = args[1];
		path = fp;
		

		String[] tpn = fp.split("/");
		pn = tpn[tpn.length - 1].substring(0, tpn[tpn.length - 1].length() - 4);
		System.out.println(pn);

		Options.v().set_src_prec(Options.src_prec_apk);
		Options.v().set_process_dir(Collections.singletonList(fp));
		Options.v().set_force_android_jar(ajar);
		Options.v().set_process_multiple_dex(true);
		Options.v().set_android_api_version(24);
		Options.v().set_output_format(Options.output_format_none);
		Options.v().set_force_overwrite(true);
		Options.v().set_allow_phantom_refs(true);
		Options.v().set_whole_program(true);
		Options.v().ignore_resolution_errors();

		Scene.v().loadNecessaryClasses();
		TimeUtility.startWatcherBruce(10 * 60);
		
		interfMthdTplt = new Hashtable<String, HashSet<String>>();
		i2c = new Hashtable<String, ArrayList<SootMethod>>();
		globalVar2MultiThrdCls = new HashMap<String, HashSet<Value>>();
		childrenTable = new HashMap<SootClass, HashSet<SootClass>>();
		runTest.ImmutableClass.add("int");
		runTest.ImmutableClass.add("short");
		runTest.ImmutableClass.add("long");
		runTest.ImmutableClass.add("byte");
		runTest.ImmutableClass.add("float");
		runTest.ImmutableClass.add("double");
		runTest.ImmutableClass.add("character");
		runTest.ImmutableClass.add("boolean");
		runTest.ImmutableClass.add("java.lang.String");
		
		runTest.intrestedSuperClass.add("android.os.Handler");
		runTest.intrestedSuperClass.add("android.os.AsyncTask");

//========Add Sinks==================
		
//		// =========== output to local storage ====================
//		
		sinkMetds.add("<java.io.DataOutputStream: void writeUTF(java.lang.String)>");
		sinkMetds.add("<java.io.DataOutputStream: void write(byte[],int,int)>");
		sinkMetds.add("<java.io.DataOutputStream: void write(java.lang.String)>");
		sinkMetds.add("<java.io.DataOutputStream: void writeBytes(java.lang.String)>");
		sinkMetds.add("<java.io.DataOutputStream: void writeChars(java.lang.String)>");
		
		sinkMetds.add("<java.io.FilterOutputStream: void writeUTF(java.lang.String)>");
		sinkMetds.add("<java.io.FilterOutputStream: void write(byte[],int,int)>");
		sinkMetds.add("<java.io.FilterOutputStream: void write(java.lang.String)>");
		sinkMetds.add("<java.io.FilterOutputStream: void writeBytes(java.lang.String)>");
		sinkMetds.add("<java.io.FilterOutputStream: void writeChars(java.lang.String)>");
		sinkMetds.add("<java.io.FilterOutputStream: void write(byte[])>");
		
		sinkMetds.add("<java.util.zip.ZipOutputStream: void writeUTF(java.lang.String)>");
		sinkMetds.add("<java.util.zip.ZipOutputStream: void write(byte[],int,int)>");
		sinkMetds.add("<java.util.zip.ZipOutputStream: void write(java.lang.String)>");
		sinkMetds.add("<java.util.zip.ZipOutputStream: void writeBytes(java.lang.String)>");
		sinkMetds.add("<java.util.zip.ZipOutputStream: void writeChars(java.lang.String)>");
		sinkMetds.add("<java.util.zip.ZipOutputStream: void write(byte[])>");
		sinkMetds.add("<java.util.zip.ZipOutputStream: void setComment(java.lang.String)>");
		
		sinkMetds.add("<java.util.zip.GZIPOutputStream: void write(byte[],int,int)>");
		sinkMetds.add("<java.util.zip.GZIPOutputStream: void writeUTF(java.lang.String)>");
		sinkMetds.add("<java.util.zip.GZIPOutputStream: void write(java.lang.String)>");
		sinkMetds.add("<java.util.zip.GZIPOutputStream: void writeBytes(java.lang.String)>");
		sinkMetds.add("<java.util.zip.GZIPOutputStream: void writeChars(java.lang.String)>");
		sinkMetds.add("<java.util.zip.GZIPOutputStream: void write(byte[])>");
//		
				
//		// ============  network ====================================
//		
		sinkMetds.add("<okhttp3.OkHttpClient: okhttp3.Call newCall(okhttp3.Request)>");
		sinkMetds.add("<okhttp3.FormBody$Builder: okhttp3.FormBody$Builder add(java.lang.String,java.lang.String)>");
		sinkMetds.add("<okhttp3.Request$Builder: okhttp3.Request$Builder post(okhttp3.RequestBody)>");
		
		sinkMetds.add("<java.net.URLConnection: void <init>(java.net.URL)>");
		sinkMetds.add("<java.net.URLConnection: void setRequestProperty(java.lang.String,java.lang.String)>");
		sinkMetds.add("<java.net.URLConnection: void addRequestProperty(java.lang.String,java.lang.String)>");
		
		sinkMetds.add("<java.net.HttpURLConnection: void <init>(java.net.URL)>");
		sinkMetds.add("<java.net.HttpURLConnection: void setRequestProperty(java.lang.String,java.lang.String)>");
		sinkMetds.add("<java.net.HttpURLConnection: void addRequestProperty(java.lang.String,java.lang.String)>");
		
		sinkMetds.add("<java.net.HttpsURLConnection: void <init>(java.net.URL)>");
		sinkMetds.add("<java.net.HttpsURLConnection: void setRequestProperty(java.lang.String,java.lang.String)>");
		sinkMetds.add("<java.net.HttpsURLConnection: void addRequestProperty(java.lang.String,java.lang.String)>");
		
		sinkMetds.add("<org.apache.http.client.methods.HttpPost: void <init>(java.net.URI)>");	//
		sinkMetds.add("<org.apache.http.client.methods.HttpPost: void <init>(java.lang.String)>");	//
		
		sinkMetds.add("<java.net.URI: void <init>(java.lang.String)>");	//
		sinkMetds.add("<java.net.URL: void <init>(java.lang.String)>");	//

		
		// =============  Comparison =================
		
		sinkMetds.add("<java.lang.Object: boolean equals(java.lang.Object)>");
		
		sinkMetds.add("<java.lang.StringBuffer: int indexOf(java.lang.String)>");
		sinkMetds.add("<java.lang.StringBuffer: int lastIndexOf(java.lang.String)>");
		
		sinkMetds.add("<java.lang.String: boolean equals(java.lang.Object)>");
		sinkMetds.add("<java.lang.String: boolean startsWith(java.lang.String)>");
		sinkMetds.add("<java.lang.String: boolean endsWith(java.lang.String)>");
		sinkMetds.add("<java.lang.String: boolean equalsIgnoreCase(java.lang.String)>");
		sinkMetds.add("<java.lang.String: boolean contentEquals(java.lang.StringBuffer)>");
		sinkMetds.add("<java.lang.String: boolean contentEquals(java.lang.CharSequence)>");
		sinkMetds.add("<java.lang.String: boolean contains(java.lang.CharSequence)>");
		sinkMetds.add("<java.lang.String: int indexOf(java.lang.String)>");
		sinkMetds.add("<java.lang.String: int indexOf(java.lang.String,int)>");
		sinkMetds.add("<java.lang.String: int lastIndexOf(java.lang.String)>");
		sinkMetds.add("<java.lang.String: int lastIndexOf(java.lang.String,int)>");
		
		sinkMetds.add("<java.lang.String: boolean isBlank()>");
		sinkMetds.add("<java.lang.String: boolean isEmpty()>");

		sinkMetds.add("<android.text.TextUtils: boolean isEmpty(java.lang.CharSequence)>");
		sinkMetds.add("<android.text.TextUtils: boolean equals(java.lang.CharSequence,java.lang.CharSequence)>");

		sinkMetds.add("<java.lang.String: boolean matches(java.lang.String)>");
		sinkMetds.add("<java.util.regex.Pattern: boolean matches(java.lang.String,java.lang.CharSequence)>");
		sinkMetds.add("<java.util.regex.Pattern: java.util.regex.Matcher matcher(java.lang.CharSequence)>");
		
//		// =========== For VSA =================
//		vsaMetds.add("<java.lang.Object: boolean equals(java.lang.Object)>");
//		
//		vsaMetds.add("<java.lang.StringBuffer: int indexOf(java.lang.String)>");
//		vsaMetds.add("<java.lang.StringBuffer: int lastIndexOf(java.lang.String)>");
//		
//		vsaMetds.add("<java.lang.String: boolean equals(java.lang.Object)>");
//		vsaMetds.add("<java.lang.String: boolean startsWith(java.lang.String)>");
//		vsaMetds.add("<java.lang.String: boolean endsWith(java.lang.String)>");
//		vsaMetds.add("<java.lang.String: boolean equalsIgnoreCase(java.lang.String)>");
//		vsaMetds.add("<java.lang.String: boolean contentEquals(java.lang.StringBuffer)>");
//		vsaMetds.add("<java.lang.String: boolean contentEquals(java.lang.CharSequence)>");
//		vsaMetds.add("<java.lang.String: boolean contains(java.lang.CharSequence)>");
//		vsaMetds.add("<java.lang.String: int indexOf(java.lang.String)>");
//		vsaMetds.add("<java.lang.String: int indexOf(java.lang.String,int)>");
//		vsaMetds.add("<java.lang.String: int lastIndexOf(java.lang.String)>");
//		vsaMetds.add("<java.lang.String: int lastIndexOf(java.lang.String,int)>");
//		
//		vsaMetds.add("<android.text.TextUtils: boolean equals(java.lang.CharSequence,java.lang.CharSequence)>");
//
//		vsaMetds.add("<java.lang.String: boolean matches(java.lang.String)>");
//		vsaMetds.add("<java.util.regex.Pattern: boolean matches(java.lang.String,java.lang.CharSequence)>");
		
		
		// =========== String manipulation ====================
		
		sinkMetds.add("<org.json.JSONObject: java.lang.String optString(java.lang.String)>");
		sinkMetds.add("<org.json.JSONObject: java.lang.String optString(java.lang.String,java.lang.String)>");
		sinkMetds.add("<org.json.JSONObject: java.lang.Object opt(java.lang.String)>");
		sinkMetds.add("<org.json.JSONObject: org.json.JSONObject optJSONObject(java.lang.String)>");
		sinkMetds.add("<java.lang.String: java.lang.String subString(int,int)>");
		
		sinkMetds.add("<java.lang.String: java.lang.String replace(java.lang.CharSequence,java.lang.CharSequence)>");
		sinkMetds.add("<java.lang.String: java.lang.String replaceAll(java.lang.String,java.lang.String)>");
		
		sinkMetds.add("<java.util.ArrayList: boolean add(java.lang.Object)>");
		sinkMetds.add("<java.util.List: boolean add(java.lang.Object)>");
		
		// =========== Key-Value Pair =====================
		sinkMetds.add("<android.content.SharedPreferences$Editor: android.content.SharedPreferences$Editor putString(java.lang.String,java.lang.String)>");
		sinkMetds.add("<android.content.SharedPreferences$Editor: android.content.SharedPreferences$Editor putStringSet(java.lang.String,java.util.Set)>");

		
//==========Add Source===================
		
		inputMetds.add("<android.content.ClipboardManager: android.content.ClipData getPrimaryClip()>");
		inputMetds.add("<android.content.ClipboardManager: java.lang.CharSequence getText()>");
		// =========== For testing ====================

		// Taint Analysis
		qg = new QuestionGenerator();
		init_taint_res = new HashSet<>();
		qg = qg.generateInputQuestions();
		
		if (qg.getTqInput().size() > 0) {
			File f = new File("./appWithCB");
			FileUtility.wf("./appWithCB", pn, true);
		}
		qg.solveInputQuestions(false);
		
		saveInitResult();

	}
	
	public static void saveInitResult() {
		
		File f = new File("./" + pn);
//		if(f.exists()) {
//			return;
//		}
		HashSet<String> taint_res = combineTaintRes(init_taint_res);

//		System.out.println("\n===============Taint Analysis Result===============\n");

//		for (String result : taint_res)
//			System.out.println(result.toString());
		

////		// String VSA
//		CallGraph.init();
//		System.out.println("\n===============String Value Analysis Result===============\n");
//		HashSet<String> strVSA_res = runStrVSA(taint_res);
////
////		System.out.println("\n===============Final Result===============\n");
////
//		for (String result : strVSA_res) {
//			System.out.println(result.toString());
//			FileUtility.wf("./" + pn, result.toString(), true);
//		}
		for (String result : taint_res) {
			System.out.println(result.toString());
			FileUtility.wf("./" + pn, result.toString(), true);
		}
	}

	public static HashSet<String> combineTaintRes(HashSet<String> taint_res) {
		Hashtable<String, String> cres = new Hashtable<String, String>();
		for (String result : taint_res) {
			JSONObject cur_json = new JSONObject(result);
			String tmp_key = cur_json.getJSONObject("source").get("unit").toString();
			tmp_key += cur_json.getJSONObject("source").get("method").toString();
			tmp_key += cur_json.getJSONObject("source").get("unitIndex").toString();
			tmp_key += cur_json.getJSONObject("source").get("RC").toString();
			tmp_key += cur_json.getJSONObject("iniPoint").get("unit").toString();
			tmp_key += cur_json.getJSONObject("iniPoint").get("method").toString();
			tmp_key += cur_json.getJSONObject("iniPoint").get("unitIndex").toString();
			if (!cres.containsKey(tmp_key)) {
				JSONObject tmp_json = new JSONObject();
				tmp_json.put("sinks", cur_json.getJSONArray("sinks"));
				tmp_json.put("source", cur_json.getJSONObject("source"));
				tmp_json.put("originsource", cur_json.getJSONObject("iniPoint"));
				cres.put(tmp_key, tmp_json.toString());
				
			} else {
				JSONObject tmp_json = new JSONObject(cres.get(tmp_key));
				for (Object nsink : cur_json.getJSONArray("sinks")) {
					boolean isHave = false;
					for (Object osink : tmp_json.getJSONArray("sinks")) {
						if (checkSinkJsonStrEquality(nsink.toString(), osink.toString())) {
							isHave = true;
							break;
						}
					}
					if (!isHave) {
						tmp_json.getJSONArray("sinks").put((JSONObject) nsink);
					}
				}
				cres.put(tmp_key, tmp_json.toString());
			}
		}
		HashSet<String> ret_res = new HashSet<String>();
		for (String tkey : cres.keySet()) {
			ret_res.add(cres.get(tkey).toString());
		}
		return ret_res;
		

	}
	
	public static void readSourceFromFile(String path) throws IOException {
        BufferedReader reader;
        reader = new BufferedReader(new FileReader(path));
        String line = reader.readLine();
        while (line != null && line.length() > 0) {
            inputMetds.add(String.join("", "<", line, ">"));
            line = reader.readLine();
        }
        reader.close();
	}

	public static boolean checkSinkJsonStrEquality(String jstr1, String jstr2) {
		JSONObject json1 = new JSONObject(jstr1);
		JSONObject json2 = new JSONObject(jstr2);
		if (!json1.getString("unit").equals(json2.getString("unit"))) {
			return false;
		} else if (!json1.getString("method").equals(json2.getString("method"))) {
			return false;
		} else if (!json1.getString("taint_var").equals(json2.getString("taint_var"))) {
			return false;
		} else if (!json1.get("unitIndex").toString().equals(json2.get("unitIndex").toString())) {
			return false;
		}
		return true;
	}

	public static HashSet<String> runStrVSA(HashSet<String> tres) {
		HashSet<String> results = null;
		HashSet<String> fresults = new HashSet<String>();
		String tmp_smtd;
		String tmp_sinstr;
		HashSet<String> tmp_tvar;
		String tmp_rinstr;

		for (String result : tres) {
			m2m = new Hashtable<String, Hashtable<String, String>>();
			JSONObject cur_json = new JSONObject(result);
			JSONArray sinks_arr = cur_json.getJSONArray("sinks");
			for (Object str : sinks_arr) {
				tmp_smtd = ((JSONObject) str).getString("method").trim();
				
				tmp_sinstr = ((JSONObject) str).getString("unit").trim();
				
				if (!hasInterestMthd(tmp_sinstr)) continue;
				
				tmp_tvar = getTvarSet(((JSONObject) str).getString("taint_var").trim());
				tmp_rinstr = tmp_sinstr;
				for (String v : tmp_tvar)
					tmp_rinstr = tmp_rinstr.replace(v, "taintedVariable");
				
				if (!m2m.containsKey(tmp_smtd)) {
					m2m.put(tmp_smtd, new Hashtable<String, String>());
				}
				if (!m2m.get(tmp_smtd).contains(tmp_rinstr)) {
					m2m.get(tmp_smtd).put(tmp_rinstr, tmp_sinstr);
				}
			}
			results = vsa(m2m);

			for (String tmp_res : results) {
				JSONObject tmp_json = new JSONObject(tmp_res);
				tmp_json.put("source", cur_json.get("source"));
				fresults.add(tmp_json.toString());
			}

			
		}
		
		return fresults;
	}
	
	public static boolean hasInterestMthd(String inst) {
		for (String iMthd : vsaMetds) {
			if (inst.contains(iMthd)) return true;
		}
		return false;
	}
	
	public static HashSet<String> getTvarSet(String tvarString) {
		HashSet<String> tmp_tvar = new HashSet<>();
		
		tvarString = tvarString.replace("[", "").replace("]", "");
		for (String v : tvarString.split(","))
			tmp_tvar.add(v.trim());
		
		return tmp_tvar;
	}

	public static HashSet<String> vsa(Hashtable<String, Hashtable<String, String>> m2m2) {

		DGraph dg = new DGraph();

		List<ValuePoint> allvps = new ArrayList<ValuePoint>();
		List<ValuePoint> vps = null;
		JSONObject tmp;

		for (String tmtd : m2m2.keySet()) {
			
			vps = ValuePoint.find(dg, tmtd, m2m2.get(tmtd), 10000);
			for (ValuePoint vp : vps) {
				// vp.print();
				allvps.add(vp);
			}
		}

		dg.solve(allvps);

		HashSet<String> result = new HashSet<String>();

		JSONObject result_json = new JSONObject();

		for (IDGNode tn : dg.getNodes()) {
			Logger.print(tn.toString());
		}

		for (ValuePoint vp : allvps) {
			tmp = vp.toJson();
			if (tmp.has("values"))
				Logger.print(tmp.getJSONArray("values").toString());
			result_json.append("sinks", vp.toJson());
		}
		// result.put("package", pn);

//		System.out.println(result_json.toString());

		if (!result.contains(result_json.toString())) {
			result.add(result_json.toString());
		}


		return result;
	}

	public static void saveFinalResult(HashSet<String> taint_res, HashSet<String> vsa_res) {
		JSONObject result = new JSONObject();
//		JSONObject tmp_result = new JSONObject();
		for (String tres : taint_res) {
			JSONObject cur_tres = new JSONObject(tres);
			result.put("package", pn);
			result.put("source", cur_tres.get("source"));

		}
	}


}
