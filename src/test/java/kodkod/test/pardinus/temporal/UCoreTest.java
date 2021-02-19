/**
 * 
 */
package kodkod.test.pardinus.temporal;

import static kodkod.test.util.Reflection.bounds;
import static kodkod.test.util.Reflection.checks;
import static kodkod.test.util.Reflection.instance;
import static kodkod.test.util.Reflection.invokeAll;
import static kodkod.test.util.Reflection.strategy;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;

import java.lang.reflect.Method;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import org.junit.Test;

import kodkod.ast.Formula;
import kodkod.engine.Proof;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.TemporalPardinusSolver;
import kodkod.engine.ltl2fol.TemporalTranslator;
import kodkod.engine.satlab.ReductionStrategy;
import kodkod.engine.satlab.SATFactory;
import kodkod.engine.ucore.RCEStrategy;
import kodkod.examples.pardinus.temporal.BasicTemporal;
import kodkod.instance.Bounds;
import kodkod.instance.PardinusBounds;
import kodkod.util.nodes.Nodes;

/**
 * Tests the unsat core functionality for temporal formulas.
 * @author Emina Torlak
 * @modified Nuno Macedo // [HASLab] temporal model finding
 */
public final class UCoreTest  {
	
	private static final Class<?>[] TEMP = {
			BasicTemporal.class,
	};

	private static final int TEMP_MAX = 4;
	
	private final TemporalPardinusSolver solver;
	private final Solver vSolver;
	
	public UCoreTest() {
		solver = new TemporalPardinusSolver();
		solver.options().setLogTranslation(1);
		solver.options().setRunTemporal(true);
		solver.options().setMaxTraceLength(5);
		solver.options().setSolver(SATFactory.MiniSatProver);		
		vSolver = new Solver();
		vSolver.options().setSolver(SATFactory.MiniSat);
	}
	
	private final void verify(Set<Formula> core, Bounds bounds, Bounds original) { 		
		TemporalTranslator tmptrns = new TemporalTranslator(Formula.and(core), (PardinusBounds) bounds, vSolver.options());
		// check that the conjunction of the high-level core formulas is false
		assertNull(vSolver.solve(tmptrns.translate(), (PardinusBounds) bounds).instance());
	
		// check that the core is minimal
		final Set<Formula> tmpCore = new LinkedHashSet<Formula>(core);
		for(Iterator<Formula> itr = core.iterator(); itr.hasNext();) {
			final Formula f = itr.next();
			tmpCore.remove(f);
			tmptrns = new TemporalTranslator(Formula.and(tmpCore), (PardinusBounds) bounds, vSolver.options());
			assertNotNull(vSolver.solve(tmptrns.translate(), (PardinusBounds) bounds).instance());
			tmpCore.add(f);
		}
		
	}
	
	private final void minimizeAndVerify(Formula formula, Bounds bounds, Proof proof, ReductionStrategy strategy) { 
		proof.minimize(strategy);
		final Set<Formula> core = Nodes.allRoots(formula, proof.highLevelCore().values().stream().map((x)->proof.log().temporalTransLog(x)).collect(Collectors.toSet()));
		final Set<Formula> tcore = proof.highLevelCore().keySet();
		verify(tcore, proof.log().bounds(),bounds);
		if (solver.options().coreGranularity()==0) { 
			assertEquals(tcore.size(), core.size());
			verify(core, proof.log().bounds(), bounds);
		} else {
			assertNull(vSolver.solve(Formula.and(core), (PardinusBounds) bounds).instance());
		}
	}
	
	private final void testProofExtractor(Class<?>[] probs, Class<? extends ReductionStrategy> strategy, int maxScope) { 
		for(Class<?> prob : probs) { 
			Object instance = instance(prob);
			Map<Method, Formula> checks = invokeAll(instance, checks(prob));
			for(Formula check : checks.values()) { 
				for(int scope = 1; scope <= maxScope; scope++ ) { 
					Bounds bounds = bounds(instance, scope);
					Solution sol = solver.solve(check, (PardinusBounds) bounds);
					if (sol.outcome()==Solution.Outcome.UNSATISFIABLE) {
						minimizeAndVerify(check, bounds, sol.proof(), strategy(strategy, sol.proof().log()));
					} 
				}
			}
			
		}
	}

	@Test
	public final void testTempRCE0() {
		solver.options().setCoreGranularity(0);
		testProofExtractor(TEMP, RCEStrategy.class, TEMP_MAX);
	}

	@Test
	public final void testTempRCE1() {
		solver.options().setCoreGranularity(1);
		testProofExtractor(TEMP, RCEStrategy.class, TEMP_MAX);
	}
	
	@Test
	public final void testTempRCE2() {
		solver.options().setCoreGranularity(2);
		testProofExtractor(TEMP, RCEStrategy.class, TEMP_MAX);
	}

	@Test
	public final void testTempRCE3() {
		solver.options().setCoreGranularity(3);
		testProofExtractor(TEMP, RCEStrategy.class, TEMP_MAX);
	}

}
