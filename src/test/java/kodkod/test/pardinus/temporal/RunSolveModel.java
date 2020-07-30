package kodkod.test.pardinus.temporal;

import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.lang.reflect.InvocationTargetException;
import java.util.Arrays;
import java.util.Iterator;

import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.DecomposedPardinusSolver;
import kodkod.engine.ExtendedSolver;
import kodkod.engine.IncrementalSolver;
import kodkod.engine.PardinusSolver;
import kodkod.engine.Solution;
import kodkod.engine.TemporalPardinusSolver;
import kodkod.engine.config.ConsoleReporter;
import kodkod.engine.config.DecomposedOptions.DMode;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.config.SLF4JReporter;
import kodkod.engine.decomp.DModel;
import kodkod.engine.decomp.DMonitor;
import kodkod.engine.ltl2fol.TemporalTranslator;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TemporalInstance;
import kodkod.instance.Universe;
import kodkod.test.pardinus.decomp.RunTests.Solvers;

public final class RunSolveModel {

    static PardinusSolver psolver;

	static Solution solution = null;
	static Iterator<Solution> solutions = null;

	static int threads, sym = 20, max_trace;
	static Solvers selected_solver;
	static DMode selected_mode;
	static private boolean batch = false;
	static DModel model;
	
	static private StringBuilder log = new StringBuilder();

	static private PrintWriter writer;

	/**
	 * Runs a partition problem model defined by the args.
	 * [PartitionModel class, mode, solver, PartitionModel args]
	 * @throws IOException
	 * @throws ClassNotFoundException
	 * @throws SecurityException
	 * @throws NoSuchMethodException
	 * @throws InvocationTargetException
	 * @throws IllegalArgumentException
	 * @throws IllegalAccessException
	 * @throws InstantiationException
	 * @throws InterruptedException 
	 */
	public static void main(String[] args) throws IOException, InstantiationException, IllegalAccessException,
	IllegalArgumentException, InvocationTargetException, NoSuchMethodException, SecurityException,
	ClassNotFoundException, InterruptedException {

		// the arguments for the partition model
		String[] model_args = Arrays.copyOfRange(args, 7, args.length);

		// dynamically create a partition model from the specified class
		model = (DModel) Class.forName(args[0]).getConstructor(String[].class)
				.newInstance((Object) model_args);
		
		// the chosen partition mode
		if (args[1].equals("BATCH"))
			batch = true;
		else
			selected_mode = DMode.valueOf(args[1]);
		// the chosen solver
		selected_solver = Solvers.valueOf(args[2]);

		max_trace = Integer.valueOf(args[3]);
		threads = Integer.valueOf(args[4]);
		
		TemporalPardinusSolver.SATOPTITERATION = Boolean.valueOf(args[5]);
		TemporalPardinusSolver.SomeDisjPattern = Boolean.valueOf(args[6]);
		
		writer = new PrintWriter(new FileWriter("pkklog.txt", true));

//		for (int i = 0; i< 200; i++)
			run_tests();

		// guarantees that every running thread is terminated.
		System.exit(0);
	}

	/**
	 * Given a partitioned model, runs the model under selected parameters.
	 * 
	 * @param model
	 * @param sym
	 * @throws InterruptedException 
	 */
	private static void run_tests() throws InterruptedException {

		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();

		ExtendedOptions opt = new ExtendedOptions();
//		opt.setReporter(new SLF4JReporter());
		opt.setBitwidth(model.getBitwidth());
		opt.setSymmetryBreaking(sym);
		opt.setMaxTraceLength(max_trace);
		if (TemporalTranslator.isTemporal(f1.and(f2)))
			opt.setRunTemporal(true);

		switch (selected_solver) {
		case GLUCOSE:
			opt.setSolver(SATFactory.Glucose);
			break;
		case MINISAT:
			opt.setSolver(SATFactory.MiniSat);
			break;
		case PLINGELING:
			opt.setSolver(SATFactory.plingeling());
			break;
		case SYRUP:
			opt.setSolver(SATFactory.syrup());
			break;
		case NUSMVB:
			opt.setSolver(SATFactory.electrod("-t","NuSMV"));
			break;
		case NUXMVB:
			opt.setSolver(SATFactory.electrod("-t","nuXmv"));
			break;
		case NUSMVC:
			opt.setRunUnbounded(true);
			opt.setSolver(SATFactory.electrod("-t","NuSMV"));
			break;
		case NUXMVC:
			opt.setRunUnbounded(true);
			opt.setSolver(SATFactory.electrod("-t","nuXmv"));
			break;
		default:
			break;
		}

		long t1 = System.currentTimeMillis();

		opt.setDecomposedMode(selected_mode);
		if (batch) {
			opt.setRunDecomposed(false);
			psolver = new PardinusSolver(opt);
//			warmup(psolver);
			solution = go_batch(b1, b2, f1, f2);
		}
		else {
			opt.setRunDecomposed(true);
			opt.configOptions().setSolver(SATFactory.Glucose);
			opt.configOptions().setRunTemporal(false);			
			psolver = new PardinusSolver(opt);
//			warmup(psolver);
			switch (selected_mode) {
			case PARALLEL:
				psolver.options().setThreads(threads);
				solution = psolver.solve(f1.and(f2), new PardinusBounds(b1, b2));
				break;
			case HYBRID:
				psolver.options().setThreads(threads);
				solution = psolver.solve(f1.and(f2), new PardinusBounds(b1, b2));
				break;
			case INCREMENTAL:
				solution = go_incremental(b1, b2, f1, f2);
				break;
			default:
				break;
			}
		}

		long t2 = System.currentTimeMillis();

//		solution = solutions.next();
		
//		for (int i = 0; i<10; i++)
//			solutions.next();
		
//		long t3 = System.currentTimeMillis();
//		
//		log.append((t3 - t2));
//		log.append("\t");
		
		if (selected_mode == DMode.PARALLEL || selected_mode == DMode.HYBRID) {
			log.append((t2 - t1));
			log.append("\t");
			log.append(solution.sat() ? "S" : "U");
			log.append("\t");
			log.append(getConfigNum(psolver));
			log.append("\t");
//			log.append(getGenTime(psolver));
//			log.append(psolution.getSolution().instance());
		}
		else {
			log.append((t2 - t1));
			log.append("\t");
			log.append(solution.sat() ? "S" : "U");
//			log.append(solution);
		}
		log.append("\t");
		flush();
	}

	private static void warmup(PardinusSolver solver) {
		Universe uni = new Universe("a");
		Relation r = Relation.unary("r");
		Relation s = Relation.unary_variable("s");
		PardinusBounds bnds1 = new PardinusBounds(uni);
		bnds1.bound(r, uni.factory().setOf("a"));
		PardinusBounds bnds2 = new PardinusBounds(uni);
		bnds2.bound(s, uni.factory().setOf("a"));
		
		for (int i = 0; i < 10; i ++)
			solver.solve(r.eq(s), new PardinusBounds(bnds1,bnds2));
	}

	private static void flush() {
//		System.out.print(log.toString());
		writer.print(log.toString());
		writer.flush();
		log = new StringBuilder();
	}

	private static long getConfigNum(PardinusSolver psolver2) {
		DMonitor mon = ((DecomposedPardinusSolver<ExtendedSolver>) psolver2.solver).executor().monitor;
		long counter = mon.getNumRuns();
		if (counter != 0)
			if (mon.isAmalgamated())
				counter = -counter;
		return counter;
	}

	/**
	 * Solves the problem under standard Kodkod (i.e., batch mode).
	 * 
	 * @param b1
	 * @param b2
	 * @param f1
	 * @param f2
	 * @return
	 */
	private static Solution go_batch(PardinusBounds b1, Bounds b2, Formula f1, Formula f2) {
		PardinusBounds x = new PardinusBounds(b1, b2);
		PardinusBounds y = x.amalgamated();

		PardinusSolver solver = new PardinusSolver(psolver.options());
		return solver.solve(f1.and(f2), y);
	}

	private static Solution go_incremental(Bounds b1, Bounds b2, Formula f1, Formula f2) {
		IncrementalSolver isolver = IncrementalSolver.solver(psolver.options());

		Bounds b3 = b1.clone();
		for (Relation r : b2.relations()) {
			b3.bound(r, b2.lowerBound(r), b2.upperBound(r));
		}
		isolver.solve(f1, b3);
		b3.relations().clear();
		return isolver.solve(f2, b3);

		// isolver.solve(f1,b1);
		// return isolver.solve(f2,b2);
	}

	
}