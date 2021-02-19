package kodkod.test.pardinus.temporal;

import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.lang.reflect.InvocationTargetException;
import java.util.Arrays;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.Explorer;
import kodkod.engine.IncrementalSolver;
import kodkod.engine.PardinusSolver;
import kodkod.engine.Solution;
import kodkod.engine.TemporalPardinusSolver;
import kodkod.engine.config.DecomposedOptions.DMode;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.decomp.DModel;
import kodkod.engine.ltl2fol.TemporalTranslator;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.PardinusBounds;
import kodkod.instance.Universe;
import kodkod.test.pardinus.temporal.RunTests.Solvers;

/**
 * CLI interface to run configuration iteration benchmarks.
 * 
 * @author Nuno Macedo
 */
public final class RunIterateCModel {

    static PardinusSolver psolver;

	static Solution solution = null;
	static Explorer<Solution> solutions = null;

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

		long t0;

		PardinusBounds x = new PardinusBounds(b1, b2);
		PardinusBounds y = x.amalgamated();

		opt.setDecomposedMode(selected_mode);
		if (batch) {
			opt.setRunDecomposed(false);
			psolver = new PardinusSolver(opt);

			PardinusSolver solver = new PardinusSolver(psolver.options());
			warmup(solver);
			t0 = System.currentTimeMillis();
			solutions = solver.solveAll(f1.and(f2), y);
			solution = solutions.next();
		}
		else {
			opt.setRunDecomposed(true);
			opt.configOptions().setSolver(SATFactory.Glucose);
			opt.configOptions().setRunTemporal(false);			
			psolver = new PardinusSolver(opt);
//			warmup(psolver);
			t0 = System.currentTimeMillis();
			switch (selected_mode) {
			case PARALLEL:
				psolver.options().setThreads(threads);
				solutions = psolver.solveAll(f1.and(f2), new PardinusBounds(b1, b2));
				solution = solutions.next();
				break;
			case HYBRID:
				psolver.options().setThreads(threads);
				solutions = psolver.solveAll(f1.and(f2), new PardinusBounds(b1, b2));
				solution = solutions.next();
				break;
			case INCREMENTAL:
				solution = go_incremental(b1, b2, f1, f2);
				break;
			default:
				break;
			}
		}
		long t11 = System.currentTimeMillis();
		
		log.append((t11 - t0));
		log.append("\t");

		if (solution.sat()) {
			
			long t1 = System.currentTimeMillis();
			int i;
			for (i=0; i<100 && solutions.hasNextC(); i++) {
				solution = solutions.nextC();
				System.out.println(i);
			}
			long t2 = System.currentTimeMillis();

			for (; i<1 && solutions.hasNextC(); i++) {
				solution = solutions.nextC();
			}
			long t22 = System.currentTimeMillis();

			log.append("S");
			log.append("\t");
			log.append(t2 - t1);
			log.append("\t");
			log.append(t22 - t1);
			log.append("\t");
			log.append(i);
		} else
			log.append("U");

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
		writer.print(log.toString());
		writer.flush();
		log = new StringBuilder();
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

	}

	
}