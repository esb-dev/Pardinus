/* 
 * Kodkod -- Copyright (c) 2005-present, Emina Torlak
 * Pardinus -- Copyright (c) 2013-present, Nuno Macedo, INESC TEC
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */

package kodkod.test.pardinus.decomp;

import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.Explorer;
import kodkod.engine.PardinusSolver;
import kodkod.engine.Solution;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TemporalInstance;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;

/**
 * As of Pardinus 1.2, non-incremental iteration is non supported.
 * 
 * @author Nuno Macedo // [HASLab] decomposed model finding
 */
public class ExplorationQualityTests {

	@Rule
    public Timeout globalTimeout = Timeout.seconds(60);

	@Test
	public void testBasic() {
		int n = 2;

		Relation a = Relation.unary_variable("a");
		Relation b = Relation.unary_variable("b");
		
		Object[] atoms = new Object[n*2];
		for (int i = 0; i < n; i ++)
			atoms[i] = "A"+i;
		for (int i = 0; i < n; i ++)
			atoms[n+i] = "B"+i;
		
		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A"+(n-1)));
		TupleSet bs = f.range(f.tuple("B0"), f.tuple("B"+(n-1)));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, as);
		bounds.bound(b, bs);
		bounds = PardinusBounds.splitAtTemporal(bounds);
		Formula formula = ((a.eq(a.prime()).not()).and(a.lone())).always().and(b.some().after()).and(b.no().always().eventually());

		ExtendedOptions opt = new ExtendedOptions();

//		opt.setReporter(new SLF4JReporter());
		opt.setRunTemporal(true);
		opt.setRunUnbounded(false);
		opt.setRunDecomposed(true);
		opt.setMaxTraceLength(10);
		opt.setSolver(SATFactory.MiniSat);
		PardinusSolver solver = new PardinusSolver(opt);
		
		Explorer<Solution> sols = (Explorer<Solution>) solver.solveAll(formula, bounds);
		Solution sol = sols.next();
		assertTrue(sol.sat());
		assertTrue(sols.hasNext());
		assertEquals(4, ((TemporalInstance) sol.instance()).prefixLength());
		opt.reporter().debug(sol.instance().toString());
		
		sol = sols.nextS(2,1, Collections.singleton(a));
		assertTrue(sol.sat());
		assertTrue(sols.hasNext());
		assertEquals(4, ((TemporalInstance) sol.instance()).prefixLength());	
		opt.reporter().debug(sol.instance().toString());

		sol = sols.nextS(2,1,Collections.singleton(a));
		assertFalse(sol.sat());
		assertTrue(sols.hasNext());

		solver.free();
	}
	
	@Test
	public void testSegIterations() {
		int n = 2;

		Relation a = Relation.unary_variable("a");
		Relation b = Relation.unary_variable("b");
		
		Object[] atoms = new Object[n*2];
		for (int i = 0; i < n; i ++)
			atoms[i] = "A"+i;
		for (int i = 0; i < n; i ++)
			atoms[n+i] = "B"+i;
		
		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A"+(n-1)));
		TupleSet bs = f.range(f.tuple("B0"), f.tuple("B"+(n-1)));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, as);
		bounds.bound(b, bs);
		bounds = PardinusBounds.splitAtTemporal(bounds);
		Formula formula = ((a.eq(a.prime()).not()).and(a.lone())).always().and(b.some().after()).and(b.no().always().eventually());

		ExtendedOptions opt = new ExtendedOptions();

//		opt.setReporter(new SLF4JReporter());
		opt.setRunTemporal(true);
		opt.setRunUnbounded(false);
		opt.setRunDecomposed(true);
		opt.setMaxTraceLength(10);
		opt.setSolver(SATFactory.MiniSat);
		PardinusSolver solver = new PardinusSolver(opt);
		
		Set<Relation> changes = new HashSet<Relation>();
		changes.add(a);
		
		Explorer<Solution> sols = (Explorer<Solution>) solver.solveAll(formula, bounds);
		Solution sol = sols.next();
		assertTrue(sol.sat());
		assertTrue(sols.hasNext());
		assertEquals(4, ((TemporalInstance) sol.instance()).prefixLength());
		opt.reporter().debug(sol.instance().toString());
		
		sol = sols.nextS(2,2, changes);
		assertTrue(sol.sat());
		assertTrue(sols.hasNext());
		assertEquals(4, ((TemporalInstance) sol.instance()).prefixLength());	
		opt.reporter().debug(sol.instance().toString());

		sol = sols.nextS(2,2, changes);
		assertTrue(sol.sat());
		assertTrue(sols.hasNext());
		assertEquals(4, ((TemporalInstance) sol.instance()).prefixLength());	
		opt.reporter().debug(sol.instance().toString());

		sol = sols.nextS(2,2, changes);
		assertTrue(sol.sat());
		assertTrue(sols.hasNext());
		assertEquals(4, ((TemporalInstance) sol.instance()).prefixLength());	
		opt.reporter().debug(sol.instance().toString());

		changes.add(b);
		sol = sols.nextS(2,2, changes);
		assertTrue(sol.sat());
		assertTrue(sols.hasNext());
		assertEquals(5, ((TemporalInstance) sol.instance()).prefixLength());	
		opt.reporter().debug(sol.instance().toString());

		sol = sols.nextS(2,2, changes);
		assertTrue(sol.sat());
		assertTrue(sols.hasNext());
		assertEquals(5, ((TemporalInstance) sol.instance()).prefixLength());	
		opt.reporter().debug(sol.instance().toString());

		sol = sols.nextS(2,2, changes);
		assertTrue(sol.sat());
		assertTrue(sols.hasNext());
		assertEquals(5, ((TemporalInstance) sol.instance()).prefixLength());	
		opt.reporter().debug(sol.instance().toString());

		sol = sols.nextS(2,2, changes);
		assertTrue(sol.sat());
		assertTrue(sols.hasNext());
		assertEquals(6, ((TemporalInstance) sol.instance()).prefixLength());	
		opt.reporter().debug(sol.instance().toString());

		sol = sols.nextS(2,2, changes);
		assertTrue(sol.sat());
		assertTrue(sols.hasNext());
		assertEquals(6, ((TemporalInstance) sol.instance()).prefixLength());	
		opt.reporter().debug(sol.instance().toString());

		sol = sols.nextS(2,2, changes);
		assertTrue(sol.sat());
		assertTrue(sols.hasNext());
		assertEquals(6, ((TemporalInstance) sol.instance()).prefixLength());	
		opt.reporter().debug(sol.instance().toString());

		sol = sols.nextS(2,2, changes);
		assertTrue(sol.sat());
		assertTrue(sols.hasNext());
		assertEquals(6, ((TemporalInstance) sol.instance()).prefixLength());	
		opt.reporter().debug(sol.instance().toString());

		sol = sols.nextS(2,2, changes);
		assertTrue(sol.sat());
		assertTrue(sols.hasNext());
		assertEquals(6, ((TemporalInstance) sol.instance()).prefixLength());	
		opt.reporter().debug(sol.instance().toString());

		sol = sols.nextS(2,2, changes);
		assertTrue(sol.sat());
		assertTrue(sols.hasNext());
		assertEquals(6, ((TemporalInstance) sol.instance()).prefixLength());	
		opt.reporter().debug(sol.instance().toString());

		changes.remove(a);
		sol = sols.nextS(4,1, changes);
		assertTrue(sol.sat());
		assertTrue(sols.hasNext());
		assertEquals(7, ((TemporalInstance) sol.instance()).prefixLength());	
		opt.reporter().debug(sol.instance().toString());

		sol = sols.nextS(4,1, changes);
		assertTrue(sol.sat());
		assertTrue(sols.hasNext());
		assertEquals(7, ((TemporalInstance) sol.instance()).prefixLength());	
		opt.reporter().debug(sol.instance().toString());

		sol = sols.nextS(4,1, changes);
		assertTrue(sol.sat());
		assertTrue(sols.hasNext());
		assertEquals(7, ((TemporalInstance) sol.instance()).prefixLength());	
		opt.reporter().debug(sol.instance().toString());

		sol = sols.nextS(4,1, changes);
		assertFalse(sol.sat());
		assertTrue(sols.hasNext());

		solver.free();
	}
	
	@Test
	public void testSegIterationsGoBack() {
		int n = 2;

		Relation a = Relation.unary_variable("a");
		Relation b = Relation.unary_variable("b");
		
		Object[] atoms = new Object[n*2];
		for (int i = 0; i < n; i ++)
			atoms[i] = "A"+i;
		for (int i = 0; i < n; i ++)
			atoms[n+i] = "B"+i;
		
		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A"+(n-1)));
		TupleSet bs = f.range(f.tuple("B0"), f.tuple("B"+(n-1)));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, as);
		bounds.bound(b, bs);
		bounds = PardinusBounds.splitAtTemporal(bounds);
		Formula formula = ((a.eq(a.prime()).not()).and(a.lone())).always().and(b.some().after()).and(b.no().always().eventually());

		ExtendedOptions opt = new ExtendedOptions();

//		opt.setReporter(new SLF4JReporter());
		opt.setRunTemporal(true);
		opt.setRunUnbounded(false);
		opt.setRunDecomposed(true);
		opt.setMaxTraceLength(10);
		opt.setSolver(SATFactory.MiniSat);
		PardinusSolver solver = new PardinusSolver(opt);
		
		Set<Relation> changes = new HashSet<Relation>();
		changes.add(a);
		
		Explorer<Solution> sols = (Explorer<Solution>) solver.solveAll(formula, bounds);
		Solution sol = sols.next();
		assertTrue(sol.sat());
		assertTrue(sols.hasNext());
		opt.reporter().debug(sol.instance().toString());
		assertEquals(4, ((TemporalInstance) sol.instance()).prefixLength());
		
		// fixes prefix up to two
		sol = sols.nextS(2,2, changes);
		assertTrue(sol.sat());
		assertTrue(sols.hasNext());
		opt.reporter().debug(sol.instance().toString());
		assertEquals(4, ((TemporalInstance) sol.instance()).prefixLength());	

		// state 1 is fixed but 2 can still change
		sol = sols.nextS(1,2, changes);
		assertTrue(sol.sat());
		assertTrue(sols.hasNext());
		opt.reporter().debug(sol.instance().toString());
		assertEquals(4, ((TemporalInstance) sol.instance()).prefixLength());	

		// state 1 cannot change
		sol = sols.nextS(1,1, changes);
		assertFalse(sol.sat());
		assertTrue(sols.hasNext());

		solver.free();
	}

	@Test
	public void testSegIterationsNoChanges() {
		int n = 2;

		Relation a = Relation.unary_variable("a");
		Relation b = Relation.unary_variable("b");
		
		Object[] atoms = new Object[n*2];
		for (int i = 0; i < n; i ++)
			atoms[i] = "A"+i;
		for (int i = 0; i < n; i ++)
			atoms[n+i] = "B"+i;
		
		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A"+(n-1)));
		TupleSet bs = f.range(f.tuple("B0"), f.tuple("B"+(n-1)));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, as);
		bounds.bound(b, bs);
		bounds = PardinusBounds.splitAtTemporal(bounds);
		Formula formula = ((a.eq(a.prime()).not()).and(a.lone())).always().and(b.some().after()).and(b.no().always().eventually());

		ExtendedOptions opt = new ExtendedOptions();

//		opt.setReporter(new SLF4JReporter());
		opt.setRunTemporal(true);
		opt.setRunUnbounded(false);
		opt.setRunDecomposed(true);
		opt.setMaxTraceLength(10);
		opt.setSolver(SATFactory.MiniSat);
		PardinusSolver solver = new PardinusSolver(opt);
		
		Explorer<Solution> sols = (Explorer<Solution>) solver.solveAll(formula, bounds);
		Solution sol = sols.next();
		assertTrue(sol.sat());
		assertTrue(sols.hasNext());
		assertEquals(4, ((TemporalInstance) sol.instance()).prefixLength());
		opt.reporter().debug(sol.instance().toString());
		
		// just fixing, solution never changes
		sol = sols.nextS(2,2, new HashSet<Relation>());
		assertFalse(sol.sat());
		assertTrue(sols.hasNext());

		// just fixing, solution never changes
		sol = sols.nextS(2,2, new HashSet<Relation>());
		assertFalse(sol.sat());
		assertTrue(sols.hasNext());

		// just fixing, solution never changes
		sol = sols.nextS(2,2, new HashSet<Relation>());
		assertFalse(sol.sat());
		assertTrue(sols.hasNext());

		// just fixing, solution never changes
		sol = sols.nextS(2,2, new HashSet<Relation>());
		assertFalse(sol.sat());
		assertTrue(sols.hasNext());

		// beyond prefix length, must unroll
		sol = sols.nextS(2,5, new HashSet<Relation>());
		assertFalse(sol.sat());
		assertTrue(sols.hasNext());

		// prefix is already fixed up to 6
		sol = sols.nextS(0,1, new HashSet<Relation>());
		assertFalse(sol.sat());
		assertTrue(sols.hasNext());
		
		// beyond the maximum trace length
		sol = sols.nextS(9,2, new HashSet<Relation>());
		assertFalse(sol.sat());
		assertTrue(sols.hasNext());
		
		solver.free();
	}

	@Test
	public void testPathIterations() {
		int n = 2;

		Relation a = Relation.unary_variable("a");
		Relation b = Relation.unary_variable("b");
		
		Object[] atoms = new Object[n*2-1];
		for (int i = 0; i < n; i ++)
			atoms[i] = "A"+i;
		for (int i = 0; i < n-1; i ++)
			atoms[n+i] = "B"+i;
		
		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A"+(n-1)));
		TupleSet bs = f.range(f.tuple("B0"), f.tuple("B"+(n-2)));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, as);
		bounds.bound(b, bs);
		bounds = PardinusBounds.splitAtTemporal(bounds);
		// always (a != a' and lone a) and some b' and eventually always no b
		Formula formula = ((a.eq(a.prime()).not()).and(a.lone())).always().and(b.some().after()).and(b.no().always().eventually());

		ExtendedOptions opt = new ExtendedOptions();

//		opt.setReporter(new SLF4JReporter());
		opt.setRunTemporal(true);
		opt.setRunUnbounded(false);
		opt.setRunDecomposed(true);
		opt.setMaxTraceLength(15);
		opt.setSolver(SATFactory.MiniSat);
		PardinusSolver solver = new PardinusSolver(opt);
		
		Explorer<Solution> sols = (Explorer<Solution>) solver.solveAll(formula, bounds);
		Solution sol = sols.next();
		assertTrue(sol.sat());
		assertTrue(sols.hasNext());
		opt.reporter().debug(sol.instance().toString());
		assertEquals(4, ((TemporalInstance) sol.instance()).prefixLength());
		
		for (int i = 0; i < 23; i++) {
			sol = sols.nextP();
			assertTrue(sol.sat());
			assertTrue(sols.hasNext());
			opt.reporter().debug(sol.instance().toString());
			assertEquals(4, ((TemporalInstance) sol.instance()).prefixLength());	
		}

		for (int i = 0; i < 96; i++) {
			sol = sols.nextP();
			assertTrue(sol.sat());
			assertTrue(sols.hasNext());
			opt.reporter().debug(sol.instance().toString());
			assertEquals(5, ((TemporalInstance) sol.instance()).prefixLength());	
		}

		solver.free();
	}
	
	@Test
	public void testPathSegIteration() {
		int n = 2;

		Relation a = Relation.unary_variable("a");
		Relation b = Relation.unary_variable("b");
		
		Object[] atoms = new Object[n*2];
		for (int i = 0; i < n; i ++)
			atoms[i] = "A"+i;
		for (int i = 0; i < n; i ++)
			atoms[n+i] = "B"+i;
		
		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A"+(n-1)));
		TupleSet bs = f.range(f.tuple("B0"), f.tuple("B"+(n-1)));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, as);
		bounds.bound(b, bs);
		bounds = PardinusBounds.splitAtTemporal(bounds);
		Formula formula = (a.lone()).always().and(b.no().always());

		ExtendedOptions opt = new ExtendedOptions();

//		opt.setReporter(new SLF4JReporter());
		opt.setRunTemporal(true);
		opt.setRunUnbounded(false);
		opt.setRunDecomposed(true);
		opt.setMaxTraceLength(10);
		opt.setSolver(SATFactory.MiniSat);
		PardinusSolver solver = new PardinusSolver(opt);
		
		Explorer<Solution> sols = (Explorer<Solution>) solver.solveAll(formula, bounds);
		Solution sol = sols.next();
		assertTrue(sol.sat());
		assertTrue(sols.hasNext());
		opt.reporter().debug(sol.instance().toString());
		assertEquals(1, ((TemporalInstance) sol.instance()).prefixLength());
		
		sol = sols.nextP();
		assertTrue(sol.sat());
		assertTrue(sols.hasNext());
		opt.reporter().debug(sol.instance().toString());
		assertEquals(1, ((TemporalInstance) sol.instance()).prefixLength());	

		sol = sols.nextS(0,1,Collections.singleton(a));
		assertTrue(sol.sat());
		assertTrue(sols.hasNext());
		opt.reporter().debug(sol.instance().toString());
		assertEquals(2, ((TemporalInstance) sol.instance()).prefixLength());	

		try {
			sol = sols.nextP();
			assertFalse(true);
		} catch (Exception e) {}

		sol = sols.nextS(0,2,Collections.singleton(a));
		assertTrue(sol.sat());
		assertTrue(sols.hasNext());
		opt.reporter().debug(sol.instance().toString());
		assertEquals(3, ((TemporalInstance) sol.instance()).prefixLength());	

		sol = sols.nextS(0,2,Collections.singleton(a));
		assertFalse(sol.sat());
		assertTrue(sols.hasNext());

		solver.free();
	}
	
	@Test
	public void testVarsWithConfig() {
		int n = 2;

		Relation a = Relation.unary("a");
		Relation b = Relation.unary_variable("b");
		
		Object[] atoms = new Object[n*2];
		for (int i = 0; i < n; i ++)
			atoms[i] = "A"+i;
		for (int i = 0; i < n; i ++)
			atoms[n+i] = "B"+i;
		
		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A"+(n-1)));
		TupleSet bs = f.range(f.tuple("B0"), f.tuple("B"+(n-1)));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, as);
		bounds.bound(b, bs);
		bounds = PardinusBounds.splitAtTemporal(bounds);
		Formula formula = a.eq(a).and(b.lone().always());

		ExtendedOptions opt = new ExtendedOptions();

//		opt.setReporter(new SLF4JReporter());
		opt.setRunTemporal(true);
		opt.setRunUnbounded(false);
		opt.setRunDecomposed(true);
		opt.setMaxTraceLength(10);
		opt.setSolver(SATFactory.MiniSat);
		PardinusSolver solver = new PardinusSolver(opt);
		
		Set<Relation> changes = new HashSet<Relation>();
		changes.add(b);
		
		Explorer<Solution> sols = (Explorer<Solution>) solver.solveAll(formula, bounds);
		Solution sol = sols.next();
		assertTrue(sol.sat());
		assertTrue(sols.hasNext());
		opt.reporter().debug(sol.instance().toString());
		assertEquals(1, ((TemporalInstance) sol.instance()).prefixLength());
		
		sol = sols.nextP();
		assertTrue(sol.sat());
		assertTrue(sols.hasNext());
		opt.reporter().debug(sol.instance().toString());
		assertEquals(1, ((TemporalInstance) sol.instance()).prefixLength());	

		for (int i = 0; i<6; i++) {
			sol = sols.nextP();
			assertTrue(sol.sat());
			assertTrue(sols.hasNext());
			opt.reporter().debug(sol.instance().toString());
			assertEquals(2, ((TemporalInstance) sol.instance()).prefixLength());	
		}

		for (int i = 0; i<4; i++) {
			sol = sols.nextS(0,2,changes);
			assertTrue(sol.sat());
			assertTrue(sols.hasNext());
			opt.reporter().debug(sol.instance().toString());
			assertEquals(3, ((TemporalInstance) sol.instance()).prefixLength());	
		}

		sol = sols.nextS(0,3,changes);
		assertTrue(sol.sat());
		assertTrue(sols.hasNext());
		opt.reporter().debug(sol.instance().toString());
		assertEquals(4, ((TemporalInstance) sol.instance()).prefixLength());	

		sol = sols.nextS(0,3,changes);
		assertFalse(sol.sat());
		assertTrue(sols.hasNext());
		
		solver.free();
	}
	
	@Test
	public void testConfig() {
		int n = 3;

		Relation a = Relation.unary("a");
		Relation b = Relation.unary_variable("b");
		
		Object[] atoms = new Object[n*2];
		for (int i = 0; i < n; i ++)
			atoms[i] = "A"+i;
		for (int i = 0; i < n; i ++)
			atoms[n+i] = "B"+i;
		
		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A"+(n-1)));
		TupleSet bs = f.range(f.tuple("B0"), f.tuple("B"+(n-1)));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, as);
		bounds.bound(b, bs);
		bounds = PardinusBounds.splitAtTemporal(bounds);
		Formula formula = a.eq(a).and(b.lone().always());

		ExtendedOptions opt = new ExtendedOptions();

//		opt.setReporter(new SLF4JReporter());
		opt.setRunTemporal(true);
		opt.setRunUnbounded(false);
		opt.setRunDecomposed(true);
		opt.setMaxTraceLength(10);
		opt.setSolver(SATFactory.MiniSat);
		PardinusSolver solver = new PardinusSolver(opt);
		
		Set<Relation> changes = new HashSet<Relation>();
		changes.add(b);
		
		Explorer<Solution> sols = (Explorer<Solution>) solver.solveAll(formula, bounds);
		Solution sol = sols.next();
		assertTrue(sol.sat());
		assertTrue(sols.hasNext());
		opt.reporter().debug(sol.instance().toString());
		assertEquals(1, ((TemporalInstance) sol.instance()).prefixLength());
		
		for (int i = 0; i < 3; i++) {
			sol = sols.nextC();
			assertTrue(sol.sat());
			assertTrue(sols.hasNext());
			opt.reporter().debug(sol.instance().toString());
			assertEquals(1, ((TemporalInstance) sol.instance()).prefixLength());	
		}

		sol = sols.nextC();
		assertFalse(sol.sat());
		assertFalse(sols.hasNextC());

		solver.free();
	}
	
	@Test
	public void testConfigPath() {
		int n = 3;

		Relation a = Relation.unary("a");
		Relation b = Relation.unary_variable("b");
		
		Object[] atoms = new Object[n*2];
		for (int i = 0; i < n; i ++)
			atoms[i] = "A"+i;
		for (int i = 0; i < n; i ++)
			atoms[n+i] = "B"+i;
		
		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A"+(n-1)));
		TupleSet bs = f.range(f.tuple("B0"), f.tuple("B"+(n-1)));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, as);
		bounds.bound(b, bs);
		bounds = PardinusBounds.splitAtTemporal(bounds);
		Formula formula = a.eq(a).and(b.lone().always());

		ExtendedOptions opt = new ExtendedOptions();

//		opt.setReporter(new SLF4JReporter());
		opt.setRunTemporal(true);
		opt.setRunUnbounded(false);
		opt.setRunDecomposed(true);
		opt.setMaxTraceLength(4);
		opt.setSolver(SATFactory.MiniSat);
		PardinusSolver solver = new PardinusSolver(opt);
		
		Set<Relation> changes = new HashSet<Relation>();
		changes.add(b);
		
		Explorer<Solution> sols = (Explorer<Solution>) solver.solveAll(formula, bounds);
		Solution sol = sols.next();
		assertTrue(sol.sat());
		assertTrue(sols.hasNext());
		opt.reporter().debug(sol.instance().toString());
		assertEquals(1, ((TemporalInstance) sol.instance()).prefixLength());
		
		for (int i = 0; i < 5; i ++) {
			sol = sols.nextP();
			assertTrue(sol.sat());
			assertTrue(sols.hasNext());
			opt.reporter().debug(sol.instance().toString());
		}

		sol = sols.nextC();
		assertTrue(sol.sat());
		assertTrue(sols.hasNext());
		opt.reporter().debug(sol.instance().toString());
		assertEquals(1, ((TemporalInstance) sol.instance()).prefixLength());	

		while (sols.hasNextP()) {
			sol = sols.nextP();
			opt.reporter().debug(sol.toString());
		}
		
		sol = sols.nextC();
		assertTrue(sol.sat());
		assertTrue(sols.hasNext());
		opt.reporter().debug(sol.instance().toString());
		assertEquals(1, ((TemporalInstance) sol.instance()).prefixLength());	

		sol = sols.nextS(0,1,Collections.singleton(b));
		assertTrue(sol.sat());
		assertTrue(sols.hasNext());
		opt.reporter().debug(sol.instance().toString());

		sol = sols.nextS(0,1,Collections.singleton(b));
		assertFalse(sol.sat());
		assertTrue(sols.hasNext());

		sol = sols.nextC();
		assertTrue(sol.sat());
		assertTrue(sols.hasNext());
		opt.reporter().debug(sol.instance().toString());
		assertEquals(1, ((TemporalInstance) sol.instance()).prefixLength());	

		sol = sols.nextC();
		assertFalse(sol.sat());
		assertFalse(sols.hasNextC());

		solver.free();
	}
}