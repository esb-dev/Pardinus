package kodkod.test.pardinus.temporal;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.text.Format;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Date;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import kodkod.engine.ExtendedSolver;
import kodkod.engine.Solution;
import kodkod.engine.config.DecomposedOptions.DMode;
import kodkod.engine.decomp.DProblem;
import kodkod.examples.pardinus.temporal.DijkstraT;
import kodkod.examples.pardinus.temporal.RingT2;
import kodkod.examples.pardinus.temporal.SpanT;
import kodkod.examples.pardinus.temporal.HotelT;

/**
 * CLI interface to run full benchmarks.
 * 
 * @author Nuno Macedo // Temporal, decomposed, unbounded, model finding and
 *         iteration
 */
public final class RunTests {

	final static Map<Integer,List<DProblem<ExtendedSolver>>> stats = new HashMap<Integer,List<DProblem<ExtendedSolver>>> ();

	static DProblem<ExtendedSolver> psolution = null;
	static Solution solution = null;

	static int tries, threads = 4, max_trace = 10, iterate = 0;
	static String timeout = "10m";

	static private boolean batch = false;
	
	static private boolean reif = false, satit = true, satonly = false, quick = false;
	
	static private StringBuilder log = new StringBuilder();

	static private PrintWriter writer;
	private static boolean ring, hotel, span, dijkstra;

	private static List<DMode> modes = new ArrayList<DMode>();
	private static List<Solvers> solvers = new ArrayList<Solvers>();

	/**
	 * @throws IOException 
	 * @throws InterruptedException 
	 */
	public static void main(String[] args) throws IOException, InterruptedException {
		List<String> opts = Arrays.asList(args);

		writer = new PrintWriter(new FileWriter("pkklog.txt", true));

		if(opts.indexOf("--tries") >= 0) tries = Integer.valueOf(opts.get(opts.indexOf("--tries")+1));
		if(opts.indexOf("--trace") >= 0) max_trace = Integer.valueOf(opts.get(opts.indexOf("--trace")+1));
		if(opts.indexOf("--timeout") >= 0) timeout = opts.get(opts.indexOf("--timeout")+1);
		
		if(opts.contains("-ms")) solvers.add(Solvers.MINISAT);
		if(opts.contains("-gl")) solvers.add(Solvers.GLUCOSE);
		if(opts.contains("-sy")) solvers.add(Solvers.SYRUP);
		if(opts.contains("-pl")) solvers.add(Solvers.PLINGELING);
		if(opts.contains("-xb")) solvers.add(Solvers.NUXMVB);
		if(opts.contains("-xc")) solvers.add(Solvers.NUXMVC);
		if(opts.contains("-sb")) solvers.add(Solvers.NUSMVB);
		if(opts.contains("-sc")) solvers.add(Solvers.NUSMVC);
		
		if(opts.contains("-b")) batch = true;
		if(opts.contains("-s")) { modes.add(DMode.PARALLEL); threads = 1;}
		if(opts.contains("-p")) modes.add(DMode.PARALLEL);
		if(opts.contains("-h")) modes.add(DMode.HYBRID);
		if(opts.contains("-i")) modes.add(DMode.INCREMENTAL);

		if(opts.contains("--quick")) quick = true;
		if(opts.contains("--satit")) satit = true;
		if(opts.contains("--reif")) reif = true;
		if(opts.contains("--iterateC")) iterate = 1;
		if(opts.contains("--iterateP")) iterate = 2;
		if(opts.contains("--satonly") || iterate > 0) satonly = true;

		if (opts.contains("--all")) {
			dijkstra = true;
			hotel = true;
			ring = true;
			span = true;
		} else {
			dijkstra = opts.contains("--dijkstra");
			hotel = opts.contains("--hotel");
			ring = opts.contains("--ring");
			span = opts.contains("--span");
		}
		
		printHeader();
		flush();

		if (dijkstra) runDijkstra();
		if (hotel) runHotel();
		if (ring) runRing();
		if (span) runSpanTree();

	}

	private static void printHeader() {
		Format formatter = new SimpleDateFormat("YYYY-MM-dd_HH-mm-ss");
		log.append("\n------\n");
		log.append(formatter.format(new Date()));
		log.append("\n");
		log.append("Analysis: ");
		log.append(iterate == 1?"IterateC ":(iterate == 2?"IterateP ":"Solve "));
		if (quick) log.append("Quick ");
		if (satonly) log.append("SatsOnly ");
		log.append("\n");
		log.append("Examples: ");
		if (hotel) log.append("Hotel ");
		if (ring) log.append("RingLeader ");
		if (span) log.append("SpanTree ");
		if (dijkstra) log.append("Dijkstra ");
		log.append("\n");

		log.append("Solvers: ");
		log.append(solvers);
		log.append("\n");

		log.append("Modes: ");
		List<String> aux = modes.stream().map(x->x.toString()).collect(Collectors.toList());
		if (batch) aux.add("BATCH");
		log.append(aux);
		log.append("\n");

		log.append("Max trace: ");
		log.append(max_trace);
		log.append("\n");

		log.append("Tries: ");
		log.append(tries);
		log.append("\n");

		log.append("Threads: ");
		log.append(threads);
		log.append("\n");

	}

	private static void flush() {
		System.out.print(log.toString());
		writer.print(log.toString());
		writer.flush();
		log = new StringBuilder();
	}
	
	private static Set<String> getCachedSolves() {
		Set<String> caches = new HashSet<>();
		BufferedReader reader;
		try {
			reader = new BufferedReader(new FileReader("../cached_solves.txt"));
			String line = reader.readLine();
			while (line != null) {
				caches.add(line);
				line = reader.readLine();
			}
			reader.close();
		} catch (FileNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return caches;
	}
	
	private static Set<String> getCachedIterateCs() {
		Set<String> caches = new HashSet<>();
		BufferedReader reader;
		try {
			reader = new BufferedReader(new FileReader("../cached_iteratecs.txt"));
			String line = reader.readLine();
			while (line != null) {
				caches.add(line);
				line = reader.readLine();
			}
			reader.close();
		} catch (FileNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return caches;
	}
	
	static Set<String> cached_timeouts_solve = getCachedSolves();
	
	static Set<String> cached_timeouts_iteratec = getCachedIterateCs();

	static Set<String> cached_timeouts_iteratep = new HashSet<>();
	
	static Map<Integer,Set<String>> cached_timeouts = Stream.of(new Object[][] { // pre-cached timeouts at 15m
	    { 0, cached_timeouts_solve },
	    { 1, cached_timeouts_iteratec },
	    { 2, cached_timeouts_iteratep }
	}).collect(Collectors.toMap(data -> (Integer) data[0], data -> (Set<String>) data[1]));
	
	/**
	 * Runs a model instance instance for the specified number of times.
	 * @throws IOException 
	 * @throws InterruptedException 
	 */
	private static int runModelInstance(String model, String[] model_args, int tries) throws IOException, InterruptedException {
		String javaHome = System.getProperty("java.home");
		String javaBin = javaHome + File.separator + "bin" + File.separator + "java";
		String classpath = System.getProperty("java.class.path");
		String className = null;
		switch (iterate) {
		case 0:
			className = RunSolveModel.class.getCanonicalName();
			break;
		case 1:
			className = RunIterateCModel.class.getCanonicalName();
			break;
		case 2:
			className = RunIteratePModel.class.getCanonicalName();
			break;
		default:
			break;
		}
		String librarypath = System.getProperty("java.library.path");

		String[] cmd_args = new String[]{"gtimeout", timeout, javaBin, "-Djava.library.path="+librarypath,"-cp", classpath, className, model};

		String[] args = Arrays.copyOf(cmd_args, cmd_args.length + model_args.length);
		System.arraycopy(model_args, 0, args, cmd_args.length, model_args.length);

		int exitVal = -1;
		
		for (int k = 0; k < tries; k++) {
			String lk = model_args[7] + " " + model_args[1] + " " + model_args[0] + " " + model_args[2] + " "+ model_args[6] + " "+ model_args[3];
			log.append(lk+ "\t");
			flush();
			boolean tos = cached_timeouts.get(iterate).contains(lk);
			if (tos) {
				log.append("**\t\t");
				if (!model_args[0].equals("BATCH")) {
					log.append("\t\t");
				}
			} else {
				Process p = Runtime.getRuntime().exec(args);
	
				InputStream stderr = p.getErrorStream();
				InputStreamReader isr = new InputStreamReader(stderr);
				BufferedReader br = new BufferedReader(isr);
				String line = null;
				while ((line = br.readLine()) != null)
					System.out.println(line);
				exitVal = p.waitFor();
				if (exitVal == 0) {
					System.out.print("OK\t\t");
					if (!model_args[0].equals("BATCH")) {
						System.out.print("\t\t");
					}
				}
				else {
	//				System.out.print("TO\t\t");
					log.append(timeout+"\t\t");
					if (!model_args[0].equals("BATCH")) {
						log.append("\t\t");
					}
					if (iterate>0) {
						log.append("\t\t");						
					}
					cached_timeouts.get(iterate).add(lk);
				}
			}
			log.append("\n");
			flush();
		}

		return exitVal;
	}

	/**
	 * Runs a model variant for the specified modes and solvers.
	 * @throws IOException 
	 * @throws InterruptedException 
	 */
	private static void runModes(String model, String[] model_args) throws IOException, InterruptedException {
		String[] args = new String[model_args.length+6];
		System.arraycopy(model_args, 0, args, 6, model_args.length);
		args[2] = max_trace+"";
		args[3] = threads+"";
		args[4] = satit+"";
		args[5] = reif+"";

		if (solvers.contains(Solvers.GLUCOSE)) {
			args[1] = Solvers.GLUCOSE.name();
			if (batch) {
				args[0] = "BATCH";
				runModelInstance(model,args,tries);
			}
			for (DMode m : modes) {
				args[0] = m.name();
				runModelInstance(model,args,tries);
			}
		}
		
		if (solvers.contains(Solvers.MINISAT)) {
			args[1] = Solvers.MINISAT.name();
			if (batch) {
				args[0] = "BATCH";
				runModelInstance(model,args,tries);
			}
			for (DMode m : modes) {
				args[0] = m.name();
				runModelInstance(model,args,tries);
			}
		}

		if (solvers.contains(Solvers.SYRUP)) {
			if (batch) {
				args[0] = "BATCH";
				args[1] = Solvers.SYRUP.name();
				runModelInstance(model,args,tries);
			}
		}

		if (solvers.contains(Solvers.PLINGELING)) {
			if (batch) {
				args[0] = "BATCH";
				args[1] = Solvers.PLINGELING.name();
				runModelInstance(model,args,tries);
			}
		}
		
		if (solvers.contains(Solvers.NUXMVB)) {
			args[1] = Solvers.NUXMVB.name();
			if (batch) {
				args[0] = "BATCH";
				runModelInstance(model,args,tries);
			}
			for (DMode m : modes) {
				args[0] = m.name();
				runModelInstance(model,args,tries);
			}
		}
		
		if (solvers.contains(Solvers.NUSMVB)) {
			args[1] = Solvers.NUSMVB.name();
			if (batch) {
				args[0] = "BATCH";
				runModelInstance(model,args,tries);
			}
			for (DMode m : modes) {
				args[0] = m.name();
				runModelInstance(model,args,tries);
			}
		}
		
		if (solvers.contains(Solvers.NUXMVC)) {
			args[1] = Solvers.NUXMVC.name();
			if (batch) {
				args[0] = "BATCH";
				runModelInstance(model,args,tries);
			}
			for (DMode m : modes) {
				args[0] = m.name();
				runModelInstance(model,args,tries);
			}
		}
		
		if (solvers.contains(Solvers.NUSMVC)) {
			args[1] = Solvers.NUSMVC.name();
			if (batch) {
				args[0] = "BATCH";
				runModelInstance(model,args,tries);
			}
			for (DMode m : modes) {
				args[0] = m.name();
				runModelInstance(model,args,tries);
			}
		}

	}

	/**
	 * Tests the performance of all variants of the Ring example.
	 * @throws IOException 
	 * @throws InterruptedException 
	 */
	private static void runRing() throws IOException, InterruptedException {
		String model = RingT2.class.getCanonicalName();

		RingT2.Variant1 v;

		if (!satonly) {  

			v = RingT2.Variant1.GOODLIVENESS;
			for (int i = 1; i <= (quick?6:8); i++) {
				runModes(model, new String[] { i + "", v.name() });
			}
			v = RingT2.Variant1.GOODSAFETY;
			for (int i = 1; i <= (quick?6:8); i++) {
				runModes(model, new String[] { i + "", v.name() });
			}
		} 
		
		v = RingT2.Variant1.BADLIVENESS;
		for (int i = 1; i <= (quick?7:12); i++) { 
			runModes(model, new String[] { i + "", v.name() });
		}

		v = RingT2.Variant1.SCENARIO;
		for (int i = 1; i <= (quick?7:12); i++) {
			runModes(model, new String[] { i + "", v.name() });
		}
		
	}

	private static void runSpanTree() throws IOException, InterruptedException {

		String model = SpanT.class.getCanonicalName();
//		int t = 9;
//		for (SpanP.Variant v : SpanP.Variant.values()) {
			SpanT.Variant v = SpanT.Variant.V1;
			for (int i = 2; i <= 16; i ++)  {
				runModes(model, new String[]{i+"",v.name()});
			}
			
			v = SpanT.Variant.V2;
			for (int i = 2; i <= 16; i ++)  {
				runModes(model, new String[]{i+"",v.name()});
			}
//		}

//		t = 12;
//		for (SpanP.Variant v : SpanP.Variant.values()) {
//			log.append("Span"+t+" "+v.name()+"\n"); 
//			log.append(header);
//			flush();
//			for (int i = 2; i <= 20; i ++)  {
//				log.append(i+"\t"); flush();
//				runModes(model, new String[]{i+"", t+"",v.name()});
//				log.append("\n"); flush();
//			}
//			log.append("\n");
//		}
	}

	private static void runDijkstra() throws IOException, InterruptedException {

		String model = DijkstraT.class.getCanonicalName();
		DijkstraT.Variant v;
		v = DijkstraT.Variant.SHOW;
		for (int i = 1; i <= (quick?11:20); i ++)  {
			runModes(model, new String[]{i+"",v.name()});
		}
		if (!satonly) {
			v = DijkstraT.Variant.DEADLOCKS;
			for (int i = 1; i <= (quick?11:20); i ++)  {
				runModes(model, new String[]{i+"",v.name()});
			}
		}
	}
	
	/**
	 * Tests the performance of all variants of the Hotel example.
	 */
	private static void runHotel() throws IOException, InterruptedException {
		String model = HotelT.class.getCanonicalName();
		HotelT.Variant v;
		if (!satonly) {
			v = HotelT.Variant.NOINTERVENES;
			for (int i = 1; i <= (quick?4:6) ; i++) {
				runModes(model, new String[] { i + "", v.name() });
			}
		}
		v = HotelT.Variant.INTERVENES;
		for (int i = 1; i <= (quick?6:10); i++) {
			runModes(model, new String[] { i + "", v.name() });
		}
	}

	public enum Solvers {
		GLUCOSE,
		MINISAT,
		SYRUP,
		PLINGELING,
		NUSMVC,
		NUXMVC,
		NUSMVB,
		NUXMVB,
	}
	

}