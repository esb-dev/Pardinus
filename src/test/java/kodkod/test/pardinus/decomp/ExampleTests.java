package kodkod.test.pardinus.decomp;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.Set;

import kodkod.ast.Formula;
import kodkod.engine.DProblemExecutorImpl;
import kodkod.engine.DecomposedPardinusSolver;
import kodkod.engine.ExtendedSolver;
import kodkod.engine.PardinusSolver;
import kodkod.engine.Solution;
import kodkod.engine.config.AbstractReporter;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.config.Reporter;
import kodkod.engine.config.DecomposedOptions.DMode;
import kodkod.engine.decomp.DModel;
import kodkod.engine.satlab.SATFactory;
import kodkod.examples.pardinus.decomp.HotelP;
import kodkod.examples.pardinus.decomp.RedBlackTreeP;
import kodkod.examples.pardinus.decomp.RingP;
import kodkod.instance.Bounds;
import kodkod.instance.PardinusBounds;
import kodkod.util.ints.IntSet;

import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;
import org.junit.rules.Timeout;

/**
 * More complex temporal model finding tests based on existing examples.
 * 
 * @author Nuno Macedo
 */
public class ExampleTests {
	PardinusSolver psolver;
	ExtendedOptions opt, opt2;

	@Rule
    public Timeout globalTimeout = Timeout.seconds(60);
	@Rule
    public final ExpectedException thrown = ExpectedException.none();

	@Before 
	public void method() throws InterruptedException {
		
		opt = new ExtendedOptions();

		opt.setRunDecomposed(true);
		opt.setSymmetryBreaking(20);
		opt.setSolver(SATFactory.Glucose);
		opt.setDecomposedMode(DMode.PARALLEL);
		opt.setThreads(4);
		opt2 = new ExtendedOptions(opt);
		opt2.setRunTarget(false);
		opt2.setSolver(SATFactory.Glucose);
		opt.setConfigOptions(opt2);
		
		Reporter rep = new AbstractReporter() {
			@Override
			public void translatingToBoolean(Formula formula, Bounds bounds) {
				System.out.println("to bool: " + formula.toString() + ", "
						+ bounds);
			}
			
			@Override
			public void detectedSymmetries(Set<IntSet> parts) {
				System.out.println("symmetry: " + parts.toString());
			}

			@Override
			public void debug(String debug) {
				System.out.println(debug);				
			}
		};
//		opt.setReporter(rep);
		psolver = new PardinusSolver(opt);
	}
	
	@Test 
	public void testSAT6Ring() throws InterruptedException {
		int n = 6;
		int t = 10;
		RingP.Variant1 v1 = RingP.Variant1.BADLIVENESS;
		RingP.Variant2 v2 = RingP.Variant2.VARIABLE;
		
		String[] args = new String[]{n+"",t+"",v1.name(),v2.name()};
		DModel model = new RingP(args);

		psolver.options().setBitwidth(model.getBitwidth());

		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1, b2));
		assertTrue(model.shortName()+": SAT", solution.sat());
		assertTrue(model.shortName()+": #Configs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs() % DProblemExecutorImpl.BATCH_SIZE == 0);
	}
	

	@Test 
	public void testUNSAT3aRing() throws InterruptedException {
		int n = 3;
		int t = 20;
		RingP.Variant1 v1 = RingP.Variant1.GOODLIVENESS;
		RingP.Variant2 v2 = RingP.Variant2.VARIABLE;
		
		String[] args = new String[]{n+"",t+"",v1.name(),v2.name()};
		DModel model = new RingP(args);

		psolver.options().setBitwidth(model.getBitwidth());

		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1, b2));
		assertFalse(model.shortName()+": SAT", solution.sat());
		assertEquals(model.shortName()+": #Runs", 8, ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns());
		assertEquals(model.shortName()+": #Configs", 8, ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs());
	}
	
	@Test 
	public void testUNSAT3bRing() throws InterruptedException {
		int n = 3;
		int t = 20;
		RingP.Variant1 v1 = RingP.Variant1.GOODSAFETY;
		RingP.Variant2 v2 = RingP.Variant2.VARIABLE;
		
		String[] args = new String[]{n+"",t+"",v1.name(),v2.name()};
		DModel model = new RingP(args);

		psolver.options().setBitwidth(model.getBitwidth());

		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1, b2));
		assertFalse(model.shortName()+": SAT", solution.sat());
		assertEquals(model.shortName()+": #Runs", 8, ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns());
		assertEquals(model.shortName()+": #Configs", 8, ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs());
	}
	
	@Test 
	public void testUNSAT4aRing() throws InterruptedException {
		int n = 4;
		int t = 20;
		RingP.Variant1 v1 = RingP.Variant1.GOODLIVENESS;
		RingP.Variant2 v2 = RingP.Variant2.VARIABLE;
		
		String[] args = new String[]{n+"",t+"",v1.name(),v2.name()};
		DModel model = new RingP(args);

		psolver.options().setBitwidth(model.getBitwidth());

		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1, b2));
		assertFalse(model.shortName()+": SAT", solution.sat());
		assertEquals(model.shortName()+": #Runs", 24, ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns());
		assertEquals(model.shortName()+": #Configs", 24, ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs());
	}
	
	@Test 
	public void testUNSAT4bRing() throws InterruptedException {
		int n = 4;
		int t = 20;
		RingP.Variant1 v1 = RingP.Variant1.GOODSAFETY;
		RingP.Variant2 v2 = RingP.Variant2.VARIABLE;
		
		String[] args = new String[]{n+"",t+"",v1.name(),v2.name()};
		DModel model = new RingP(args);

		psolver.options().setBitwidth(model.getBitwidth());

		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1, b2));
		assertFalse(model.shortName()+": SAT", solution.sat());
		assertEquals(model.shortName()+": #Runs", 24, ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns());
		assertEquals(model.shortName()+": #Configs", 24, ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs());
	}
	
	@Test 
	public void testHSAT9Ring() throws InterruptedException {
		int n = 9;
		int t = 20;
		RingP.Variant1 v1 = RingP.Variant1.BADLIVENESS;
		RingP.Variant2 v2 = RingP.Variant2.VARIABLE;
		psolver.options().setDecomposedMode(DMode.HYBRID);

		String[] args = new String[]{n+"",t+"",v1.name(),v2.name()};
		DModel model = new RingP(args);

		psolver.options().setBitwidth(model.getBitwidth());

		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1, b2));
		assertTrue(model.shortName()+": SAT", solution.sat());
//		assertTrue(model.shortName()+": #Runs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns() < 415);
//		assertTrue(model.shortName()+": #Configs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs() <= 415);
//		assertEquals(model.shortName()+": Amalg", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.isAmalgamated(), true);
	}
	
	@Test 
	public void testHSAT6Ring() throws InterruptedException {
		int n = 6;
		int t = 20;
		RingP.Variant1 v1 = RingP.Variant1.BADLIVENESS;
		RingP.Variant2 v2 = RingP.Variant2.VARIABLE;
		psolver.options().setDecomposedMode(DMode.HYBRID);

		String[] args = new String[]{n+"",t+"",v1.name(),v2.name()};
		DModel model = new RingP(args);

		psolver.options().setBitwidth(model.getBitwidth());

		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1, b2));
		assertTrue(model.shortName()+": SAT", solution.sat());
		assertTrue(model.shortName()+": #Runs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns() < 415);
		assertTrue(model.shortName()+": #Configs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs() <= 415);
//		assertTrue(model.shortName()+": Amalg", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.isAmalgamated());
	}
	

	@Test 
	public void testHUNSAT3aRing() throws InterruptedException {
		int n = 3;
		int t = 20;
		RingP.Variant1 v1 = RingP.Variant1.GOODLIVENESS;
		RingP.Variant2 v2 = RingP.Variant2.VARIABLE;
		psolver.options().setDecomposedMode(DMode.HYBRID);
	
		String[] args = new String[]{n+"",t+"",v1.name(),v2.name()};
		DModel model = new RingP(args);

		psolver.options().setBitwidth(model.getBitwidth());

		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1, b2));
		assertFalse(model.shortName()+": SAT", solution.sat());
//		assertTrue(model.shortName()+": Amalg", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.isAmalgamated());
		assertTrue(model.shortName()+": #Runs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns() <= 9);
		assertTrue(model.shortName()+": #Configs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs() <= 8);
	}
	
	@Test 
	public void testHUNSAT3bRing() throws InterruptedException {
		int n = 3;
		int t = 20;
		RingP.Variant1 v1 = RingP.Variant1.GOODSAFETY;
		RingP.Variant2 v2 = RingP.Variant2.VARIABLE;
		psolver.options().setDecomposedMode(DMode.HYBRID);
		
		String[] args = new String[]{n+"",t+"",v1.name(),v2.name()};
		DModel model = new RingP(args);

		psolver.options().setBitwidth(model.getBitwidth());

		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1, b2));
		assertFalse(model.shortName()+": SAT", solution.sat());
//		assertTrue(model.shortName()+": Amalg", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.isAmalgamated());
		assertTrue(model.shortName()+": #Runs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns() <= 9);
		assertTrue(model.shortName()+": #Configs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs() <= 8);
	}
	
	@Test 
	public void testHUNSAT4aRing() throws InterruptedException {
		int n = 4;
		int t = 20;
		RingP.Variant1 v1 = RingP.Variant1.GOODLIVENESS;
		RingP.Variant2 v2 = RingP.Variant2.VARIABLE;
		psolver.options().setDecomposedMode(DMode.HYBRID);
	
		String[] args = new String[]{n+"",t+"",v1.name(),v2.name()};
		DModel model = new RingP(args);

		psolver.options().setBitwidth(model.getBitwidth());

		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1, b2));
		assertFalse(model.shortName()+": SAT", solution.sat());
//		assertTrue(model.shortName()+": Amalg", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.isAmalgamated());
		assertTrue(model.shortName()+": #Runs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns() <= 25);
		assertTrue(model.shortName()+": #Configs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs() <= 24);
	}
	
	@Test 
	public void testHUNSAT4bRing() throws InterruptedException {
		int n = 4;
		int t = 20;
		RingP.Variant1 v1 = RingP.Variant1.GOODSAFETY;
		RingP.Variant2 v2 = RingP.Variant2.VARIABLE;
		psolver.options().setDecomposedMode(DMode.HYBRID);
	
		String[] args = new String[]{n+"",t+"",v1.name(),v2.name()};
		DModel model = new RingP(args);

		psolver.options().setBitwidth(model.getBitwidth());

		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1, b2));
		assertFalse(model.shortName()+": SAT", solution.sat());
//		assertTrue(model.shortName()+": Amalg", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.isAmalgamated());
		assertTrue(model.shortName()+": #Runs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns() <= 25);
		assertTrue(model.shortName()+": #Configs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs() <= 24);
	}
	
	@Test 
	public void testSAT3Hotel() throws InterruptedException {
		int n = 3;
		int t = 20;
		HotelP.Variant v1 = HotelP.Variant.INTERVENES;
		
		String[] args = new String[]{n+"",t+"",v1.name()};
		DModel model = new HotelP(args);

		opt.setBitwidth(model.getBitwidth());
		opt.setSkolemDepth(-1);
		opt.setRunDecomposed(true);

		PardinusSolver psolver = new PardinusSolver(opt);
		
		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1,b2));
		
		long configs = ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs();
		
		assertTrue(model.shortName()+": SAT", solution.sat());
		assertEquals(model.shortName()+": #Configs", 20, configs);
		
	}
	
	@Test 
	public void testSAT4Hotel() throws InterruptedException {
		int n = 4;
		int t = 20;
		HotelP.Variant v1 = HotelP.Variant.INTERVENES;
		
		String[] args = new String[]{n+"",t+"",v1.name()};
		DModel model = new HotelP(args);

		opt.setBitwidth(model.getBitwidth());
		opt.setRunDecomposed(true);

		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		PardinusSolver psolver = new PardinusSolver(opt);

		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1,b2));
		
		long configs = ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs();

		assertTrue(model.shortName()+": SAT", solution.sat());
		assertEquals(model.shortName()+": #Configs", Math.min(75,DProblemExecutorImpl.BATCH_SIZE), configs);

	}
	
	@Test 
	public void testSAT5Hotel() throws InterruptedException {
		int n = 5;
		int t = 20;
		HotelP.Variant v1 = HotelP.Variant.INTERVENES;
		
		String[] args = new String[]{n+"",t+"",v1.name()};
		DModel model = new HotelP(args);

		opt.setBitwidth(model.getBitwidth());
		opt.setRunDecomposed(true);
		
		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		PardinusSolver psolver = new PardinusSolver(opt);

		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1,b2));
		
		long configs = ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs();

		assertTrue(model.shortName()+": SAT", solution.sat());
		// >200, but decomp launches batches of 20
		assertEquals(model.shortName()+": #Configs", DProblemExecutorImpl.BATCH_SIZE, configs);
	}
	
	@Test 
	public void testUNSAT3Hotel() throws InterruptedException {
		int n = 3;
		int t = 10;
		HotelP.Variant v1 = HotelP.Variant.NOINTERVENES;
		
		String[] args = new String[]{n+"",t+"",v1.name()};
		DModel model = new HotelP(args);

		opt.setBitwidth(model.getBitwidth());
		opt.setRunDecomposed(true);
		
		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();

		PardinusSolver psolver = new PardinusSolver(opt);

		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1,b2));
		
		long configs = ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs();
		long runs = ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns();

		assertFalse(model.shortName()+": SAT", solution.sat());
		assertEquals(model.shortName()+": #Runs", 20, runs);
		assertEquals(model.shortName()+": #Configs", 20, configs);
	}
	
	@Test 
	public void testHSAT3Hotel() throws InterruptedException {
		int n = 3;
		int t = 20;
		HotelP.Variant v1 = HotelP.Variant.INTERVENES;
		opt.setDecomposedMode(DMode.HYBRID);
		
		String[] args = new String[]{n+"",t+"",v1.name()};
		DModel model = new HotelP(args);

		opt.setBitwidth(model.getBitwidth());
		opt.setRunDecomposed(true);
		
		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();

		PardinusSolver psolver = new PardinusSolver(opt);

		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1,b2));
		
		long configs = ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs();
		long runs = ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns();
		boolean amalgamated = ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.isAmalgamated();

		assertTrue(model.shortName()+": SAT", solution.sat());
		assertTrue(model.shortName()+": #Configs", configs <= 20);
		assertTrue(model.shortName()+": #Runs", runs < 20);
		assertFalse(model.shortName()+": Amalg", amalgamated);
	}
	
	@Test 
	public void testHSAT4Hotel() throws InterruptedException {
		int n = 4;
		int t = 20;
		HotelP.Variant v1 = HotelP.Variant.INTERVENES;
		opt.setDecomposedMode(DMode.HYBRID);

		String[] args = new String[]{n+"",t+"",v1.name()};
		DModel model = new HotelP(args);

		opt.setBitwidth(model.getBitwidth());
		opt.setRunDecomposed(true);
		
		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		PardinusSolver psolver = new PardinusSolver(opt);

		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1,b2));

		long configs = ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs();
		long runs = ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns();
		boolean amalgamated = ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.isAmalgamated();

		assertTrue(model.shortName()+": SAT", solution.sat());
		assertTrue(model.shortName()+": #Configs", configs <= 75);
		assertTrue(model.shortName()+": #Runs", runs < 75);
		assertFalse(model.shortName()+": Amalg", amalgamated);
	}
	
	@Test 
	public void testHUNSAT3Hotel() throws InterruptedException {
		int n = 3;
		int t = 10;
		HotelP.Variant v1 = HotelP.Variant.NOINTERVENES;
		opt.setDecomposedMode(DMode.HYBRID);

		String[] args = new String[]{n+"",t+"",v1.name()};
		DModel model = new HotelP(args);

		opt.setBitwidth(model.getBitwidth());
		opt.setRunDecomposed(true);
		
		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		PardinusSolver psolver = new PardinusSolver(opt);

		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1,b2));
		
		long configs = ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs();
		long runs = ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns();
		boolean amalgamated = ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.isAmalgamated();

		assertFalse(model.shortName()+": SAT", solution.sat());
		assertTrue(model.shortName()+": #Configs", configs <= 20);
		assertTrue(model.shortName()+": #Runs", runs < 20);
//		assertTrue(model.shortName()+": Amalg", amalgamated);
	}
	
	@Test 
	public void testHUNSAT4Hotel() throws InterruptedException {
		int n = 4;
		int t = 10;
		HotelP.Variant v1 = HotelP.Variant.NOINTERVENES;
		opt.setDecomposedMode(DMode.HYBRID);

		String[] args = new String[]{n+"",t+"",v1.name()};
		DModel model = new HotelP(args);

		opt.setBitwidth(model.getBitwidth());
		opt.setRunDecomposed(true);
		
		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		PardinusSolver psolver = new PardinusSolver(opt);

		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1,b2));
		
		long configs = ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs();
		long runs = ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns();
		boolean amalgamated = ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.isAmalgamated();

		assertFalse(model.shortName()+": SAT", solution.sat());
		assertTrue(model.shortName()+": #Configs", configs <= 75);
		assertTrue(model.shortName()+": #Runs", runs < 75);
//		assertTrue(model.shortName()+": Amalg", amalgamated);
	}	

	@Test 
	public void testSAT3RBT() throws InterruptedException {
		opt.setDecomposedMode(DMode.PARALLEL);
		int n = 3;
		RedBlackTreeP.Variant1 v1 = RedBlackTreeP.Variant1.COUNTER;
		RedBlackTreeP.Variant2 v2 = RedBlackTreeP.Variant2.V1;
		
		String[] args = new String[]{n+"",v1.name(),v2.name()};
		DModel model = new RedBlackTreeP(args);

		opt.setBitwidth(model.getBitwidth());
		opt2.setBitwidth(model.getBitwidth());
		
		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1, b2));
		assertTrue(model.shortName()+": SAT", solution.sat());
		assertTrue(model.shortName()+": #Runs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns() <= 5);
		assertEquals(model.shortName()+": #Configs", 5, ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs());
	}
	
	@Test 
	public void testSAT4RBT() throws InterruptedException {
		opt.setDecomposedMode(DMode.PARALLEL);
		int n = 4;
		RedBlackTreeP.Variant1 v1 = RedBlackTreeP.Variant1.COUNTER;
		RedBlackTreeP.Variant2 v2 = RedBlackTreeP.Variant2.V1;
		
		String[] args = new String[]{n+"",v1.name(),v2.name()};
		DModel model = new RedBlackTreeP(args);

		opt.setBitwidth(model.getBitwidth());
		opt2.setBitwidth(model.getBitwidth());
		
		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1, b2));
		assertTrue(model.shortName()+": SAT", solution.sat());
		assertTrue(model.shortName()+": #Runs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns() <= 14);
		assertEquals(model.shortName()+": #Configs", 14, ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs());
	}
	
	@Test 
	public void testSAT5RBT() throws InterruptedException {
		opt.setDecomposedMode(DMode.PARALLEL);
		int n = 5;
		RedBlackTreeP.Variant1 v1 = RedBlackTreeP.Variant1.COUNTER;
		RedBlackTreeP.Variant2 v2 = RedBlackTreeP.Variant2.V1;

		String[] args = new String[]{n+"",v1.name(),v2.name()};
		DModel model = new RedBlackTreeP(args);

		opt.setBitwidth(model.getBitwidth()+2);
		opt2.setBitwidth(model.getBitwidth()+2);
		
		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1, b2));
//		System.out.println(solution.instance());
		assertTrue(model.shortName()+": SAT", solution.sat());
		assertTrue(model.shortName()+": #Runs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns() <= 42);
		assertTrue(model.shortName()+": #Configs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs() <= 42);
	}
	
	@Test 
	public void testSAT6RBT() throws InterruptedException {
		opt.setDecomposedMode(DMode.PARALLEL);
		int n = 6;
		RedBlackTreeP.Variant1 v1 = RedBlackTreeP.Variant1.COUNTER;
		RedBlackTreeP.Variant2 v2 = RedBlackTreeP.Variant2.V1;
		
		String[] args = new String[]{n+"",v1.name(),v2.name()};
		DModel model = new RedBlackTreeP(args);

		opt.setBitwidth(model.getBitwidth());
		opt2.setBitwidth(model.getBitwidth());
		
		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1, b2));
		assertTrue(model.shortName()+": SAT", solution.sat());
		assertTrue(model.shortName()+": #Runs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns() <= 132);
		// 132, but decomp launches batches of 50
		assertTrue(model.shortName()+": #Configs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs() / 50 <= 2);
	}
	
	@Test 
	public void testUNSAT3RBT() throws InterruptedException {
		opt.setDecomposedMode(DMode.PARALLEL);
		int n = 3;
		RedBlackTreeP.Variant1 v1 = RedBlackTreeP.Variant1.THEOREM;
		RedBlackTreeP.Variant2 v2 = RedBlackTreeP.Variant2.V1;
		
		String[] args = new String[]{n+"",v1.name(),v2.name()};
		DModel model = new RedBlackTreeP(args);

		opt.setBitwidth(model.getBitwidth());
		opt2.setBitwidth(model.getBitwidth());
		
		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1, b2));
		assertFalse(model.shortName()+": SAT", solution.sat());
//		assertEquals(model.shortName()+": #Runs", 5, ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns());
//		assertEquals(model.shortName()+": #Configs", 5, ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs());
		assertEquals(model.shortName()+": #Runs", 4, ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns());
		assertEquals(model.shortName()+": #Configs", 4, ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs());
	}
	
	@Test 
	public void testUNSAT4RBT() throws InterruptedException {
		opt.setDecomposedMode(DMode.PARALLEL);
		int n = 4;
		RedBlackTreeP.Variant1 v1 = RedBlackTreeP.Variant1.THEOREM;
		RedBlackTreeP.Variant2 v2 = RedBlackTreeP.Variant2.V1;
		
		String[] args = new String[]{n+"",v1.name(),v2.name()};
		DModel model = new RedBlackTreeP(args);

		opt.setBitwidth(model.getBitwidth());
		opt2.setBitwidth(model.getBitwidth());
		
		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1, b2));
		assertFalse(model.shortName()+": SAT", solution.sat());
//		assertEquals(model.shortName()+": #Runs", 14, ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns());
//		assertEquals(model.shortName()+": #Configs", 14, ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs());
		assertEquals(model.shortName()+": #Runs", 28, ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns());
		assertEquals(model.shortName()+": #Configs", 28, ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs());
	}
	
	@Test 
	public void testUNSAT5RBT() throws InterruptedException {
		opt.setDecomposedMode(DMode.PARALLEL);
		int n = 5;
		RedBlackTreeP.Variant1 v1 = RedBlackTreeP.Variant1.THEOREM;
		RedBlackTreeP.Variant2 v2 = RedBlackTreeP.Variant2.V1;
		
		String[] args = new String[]{n+"",v1.name(),v2.name()};
		DModel model = new RedBlackTreeP(args);

		opt.setBitwidth(model.getBitwidth());
		opt2.setBitwidth(model.getBitwidth());

		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1, b2));
		assertFalse(model.shortName()+": SAT", solution.sat());
//		assertEquals(model.shortName()+": #Runs", 42, ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns());
//		assertEquals(model.shortName()+": #Configs", 42, ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs());
		assertEquals(model.shortName()+": #Runs", 152, ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns());
		assertEquals(model.shortName()+": #Configs", 152, ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs());
	}
	
	@Test 
	public void testHSAT3RBT() throws InterruptedException {
		int n = 3;
		RedBlackTreeP.Variant1 v1 = RedBlackTreeP.Variant1.COUNTER;
		RedBlackTreeP.Variant2 v2 = RedBlackTreeP.Variant2.V1;
		psolver.options().setDecomposedMode(DMode.HYBRID);
	
		String[] args = new String[]{n+"",v1.name(),v2.name()};
		DModel model = new RedBlackTreeP(args);

		opt.setBitwidth(model.getBitwidth());
		opt2.setBitwidth(model.getBitwidth());
		
		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1, b2));
		assertTrue(model.shortName()+": SAT", solution.sat());
		assertTrue(model.shortName()+": #Configs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs() <= 5);
		assertTrue(model.shortName()+": #Runs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns() <= 6);
//		assertTrue(model.shortName()+": Amalg", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.isAmalgamated());
	}
	
	@Test 
	public void testHSAT4RBT() throws InterruptedException {
		int n = 4;
		RedBlackTreeP.Variant1 v1 = RedBlackTreeP.Variant1.COUNTER;
		RedBlackTreeP.Variant2 v2 = RedBlackTreeP.Variant2.V1;
		psolver.options().setDecomposedMode(DMode.HYBRID);
	
		String[] args = new String[]{n+"",v1.name(),v2.name()};
		DModel model = new RedBlackTreeP(args);

		opt.setBitwidth(model.getBitwidth());
		opt2.setBitwidth(model.getBitwidth());
		
		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1, b2));
		assertTrue(model.shortName()+": SAT", solution.sat());
		assertTrue(model.shortName()+": #Configs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs() <= 14);
		assertTrue(model.shortName()+": #Runs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns() < 14);
//		assertEquals(model.shortName()+": Amalg", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.isAmalgamated(), true);
	}
	
	@Test 
	public void testHSAT5RBT() throws InterruptedException {
		int n = 5;
		RedBlackTreeP.Variant1 v1 = RedBlackTreeP.Variant1.COUNTER;
		RedBlackTreeP.Variant2 v2 = RedBlackTreeP.Variant2.V1;
		psolver.options().setDecomposedMode(DMode.HYBRID);
	
		String[] args = new String[]{n+"",v1.name(),v2.name()};
		DModel model = new RedBlackTreeP(args);

		opt.setBitwidth(model.getBitwidth());
		opt2.setBitwidth(model.getBitwidth());
		
		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1, b2));
		assertTrue(model.shortName()+": SAT", solution.sat());
		assertTrue(model.shortName()+": #Configs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs() <= 42);
		assertTrue(model.shortName()+": #Runs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns() < 42);
//		assertTrue(model.shortName()+": Amalg", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.isAmalgamated());
	}
	
	@Test 
	public void testHSAT6RBT() throws InterruptedException {
		int n = 6;
		RedBlackTreeP.Variant1 v1 = RedBlackTreeP.Variant1.COUNTER;
		RedBlackTreeP.Variant2 v2 = RedBlackTreeP.Variant2.V1;
		psolver.options().setDecomposedMode(DMode.HYBRID);
	
		String[] args = new String[]{n+"",v1.name(),v2.name()};
		DModel model = new RedBlackTreeP(args);

		opt.setBitwidth(model.getBitwidth());
		opt2.setBitwidth(model.getBitwidth());
		
		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1, b2));
		assertTrue(model.shortName()+": SAT", solution.sat());
		assertTrue(model.shortName()+": #Configs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs() <= 132);
		assertTrue(model.shortName()+": #Runs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns() < 132);
//		assertTrue(model.shortName()+": Amalg", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.isAmalgamated());
	}
	
	@Test 
	public void testHUNSAT3RBT() throws InterruptedException {
		int n = 3;
		RedBlackTreeP.Variant1 v1 = RedBlackTreeP.Variant1.THEOREM;
		RedBlackTreeP.Variant2 v2 = RedBlackTreeP.Variant2.V1;
		psolver.options().setDecomposedMode(DMode.HYBRID);
	
		String[] args = new String[]{n+"",v1.name(),v2.name()};
		DModel model = new RedBlackTreeP(args);

		opt.setBitwidth(model.getBitwidth());
		opt2.setBitwidth(model.getBitwidth());
		
		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1, b2));
		assertFalse(model.shortName()+": SAT", solution.sat());
		assertTrue(model.shortName()+": #Configs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs() <= 4);
		assertTrue(model.shortName()+": #Runs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns() <= 5);
//		assertTrue(model.shortName()+": Amalg", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.isAmalgamated());
	}
	
	@Test 
	public void testHUNSAT4RBT() throws InterruptedException {
		int n = 4;
		RedBlackTreeP.Variant1 v1 = RedBlackTreeP.Variant1.THEOREM;
		RedBlackTreeP.Variant2 v2 = RedBlackTreeP.Variant2.V1;
		psolver.options().setDecomposedMode(DMode.HYBRID);
	
		String[] args = new String[]{n+"",v1.name(),v2.name()};
		DModel model = new RedBlackTreeP(args);

		opt.setBitwidth(model.getBitwidth());
		opt2.setBitwidth(model.getBitwidth());

		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1, b2));
		assertEquals(model.shortName()+": SAT", solution.sat(), false);
		assertTrue(model.shortName()+": #Configs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs() <= 28);
		assertTrue(model.shortName()+": #Runs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns() < 29);
//		assertTrue(model.shortName()+": Amalg", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.isAmalgamated());
	}
	
	@Test 
	public void testHUNSAT5RBT() throws InterruptedException {
		int n = 5;
		RedBlackTreeP.Variant1 v1 = RedBlackTreeP.Variant1.THEOREM;
		RedBlackTreeP.Variant2 v2 = RedBlackTreeP.Variant2.V1;
		psolver.options().setDecomposedMode(DMode.HYBRID);
	
		String[] args = new String[]{n+"",v1.name(),v2.name()};
		DModel model = new RedBlackTreeP(args);

		opt.setBitwidth(model.getBitwidth());
		opt2.setBitwidth(model.getBitwidth());
		
		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1, b2));
		assertFalse(model.shortName()+": SAT", solution.sat());
		assertTrue(model.shortName()+": #Configs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs() <= 152);
		assertTrue(model.shortName()+": #Runs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns() < 153);
//		assertTrue(model.shortName()+": Amalg", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.isAmalgamated());
	}
	
	@Test 
	public void testHUNSAT6RBT() throws InterruptedException {
		int n = 6;
		RedBlackTreeP.Variant1 v1 = RedBlackTreeP.Variant1.THEOREM;
		RedBlackTreeP.Variant2 v2 = RedBlackTreeP.Variant2.V1;
		psolver.options().setDecomposedMode(DMode.HYBRID);
	
		String[] args = new String[]{n+"",v1.name(),v2.name()};
		DModel model = new RedBlackTreeP(args);

		opt.setBitwidth(model.getBitwidth());
		opt2.setBitwidth(model.getBitwidth());
		
		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1, b2));
		assertFalse(model.shortName()+": SAT", solution.sat());
		assertTrue(model.shortName()+": #Configs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs() <= 748);
		assertTrue(model.shortName()+": #Runs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns() <= 749);
//		assertTrue(model.shortName()+": Amalg", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.isAmalgamated());
	}
}
