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
package kodkod.test.pardinus.temporal;

import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.PardinusSolver;
import kodkod.engine.Solution;
import kodkod.engine.Solution.Outcome;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import org.junit.BeforeClass;
import org.junit.Test;

/**
 * Basic tests to check whether the temporal bounded engine is running.
 * 
 * @author Nuno Macedo // [HASLab] temporal model finding
 */
public class BaseTests {
	
	private static PardinusSolver dsolver;
	private static ExtendedOptions opt;

	@BeforeClass
	public static void method() throws InterruptedException {
		opt = new ExtendedOptions();
		opt.setSymmetryBreaking(20);
		opt.setRunDecomposed(false);
	}

	@Test
	public void testSatSAT() {
		opt.setSolver(SATFactory.MiniSat);
		opt.setRunTemporal(true);
		opt.setRunUnbounded(false);
		dsolver = new PardinusSolver(opt);
		opt.setMinTraceLength(2);
		opt.setMaxTraceLength(10);

		int n = 2;

		Relation a = Relation.unary_variable("a");
		Relation b = Relation.unary("b");
		Relation r = Relation.binary_variable("r");

		Object[] atoms = new Object[n * 2];
		for (int i = 0; i < n; i++)
			atoms[i] = "A" + i;
		for (int i = 0; i < n; i++)
			atoms[n + i] = "B" + i;

		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A" + (n - 1)));
		TupleSet bs = f.range(f.tuple("B0"), f.tuple("B" + (n - 1)));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, as);
		bounds.bound(b, bs);
		bounds.bound(r, a.product(b));
		Formula formula = ((a.eq(a.prime()).not())).and(r.lone()).always();
		Formula run = a.no().eventually();
		
		Solution sol = dsolver.solveAll(formula.and(run), bounds).next();
		
		assertTrue("base problem should be sat", sol.sat());
	}
	
	@Test
	public void testUnsatSAT() {
		opt.setSolver(SATFactory.MiniSat);
		opt.setRunTemporal(true);
		opt.setRunUnbounded(false);
		dsolver = new PardinusSolver(opt);

		int n = 2;

		Relation a = Relation.unary_variable("a");
		Relation b = Relation.unary("b");
		Relation r = Relation.binary_variable("r");

		Object[] atoms = new Object[n * 2];
		for (int i = 0; i < n; i++)
			atoms[i] = "A" + i;
		for (int i = 0; i < n; i++)
			atoms[n + i] = "B" + i;

		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A" + (n - 1)));
		TupleSet bs = f.range(f.tuple("B0"), f.tuple("B" + (n - 1)));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, as);
		bounds.bound(b, bs);
		bounds.bound(r, a.product(b));
		Formula formula = ((a.eq(a.prime()).not())).and(r.some()).always();
		Formula run = r.no().eventually();
		
		Solution sol = dsolver.solveAll(formula.and(run), bounds).next();
		
		assertFalse("base problem should be unsat",sol.sat());
	}
	
	@Test
	public void testSatSATLength() {
		opt.setSolver(SATFactory.MiniSat);
		opt.setRunTemporal(true);
		opt.setRunUnbounded(false);
		opt.setMinTraceLength(10);
		opt.setMaxTraceLength(20);
		dsolver = new PardinusSolver(opt);

		int n = 2;

		Relation a = Relation.unary_variable("a");
		Relation b = Relation.unary("b");
		Relation r = Relation.binary_variable("r");

		Object[] atoms = new Object[n * 2];
		for (int i = 0; i < n; i++)
			atoms[i] = "A" + i;
		for (int i = 0; i < n; i++)
			atoms[n + i] = "B" + i;

		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A" + (n - 1)));
		TupleSet bs = f.range(f.tuple("B0"), f.tuple("B" + (n - 1)));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, as);
		bounds.bound(b, bs);
		bounds.bound(r, a.product(b));
		Formula formula = ((a.eq(a.prime()).not())).and(r.lone()).always();
		Formula run = a.no().eventually();
		
		Solution sol = dsolver.solveAll(formula.and(run), bounds).next();
		
		assertTrue("base problem should be sat for this trace length", sol.sat());
	}
	
	@Test
	public void testUnsatSATLength() {
		opt.setSolver(SATFactory.MiniSat);
		opt.setRunTemporal(true);
		opt.setRunUnbounded(false);
		opt.setMinTraceLength(1);
		opt.setMaxTraceLength(1);
		dsolver = new PardinusSolver(opt);

		int n = 2;

		Relation a = Relation.unary_variable("a");
		Relation b = Relation.unary("b");
		Relation r = Relation.binary_variable("r");

		Object[] atoms = new Object[n * 2];
		for (int i = 0; i < n; i++)
			atoms[i] = "A" + i;
		for (int i = 0; i < n; i++)
			atoms[n + i] = "B" + i;

		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A" + (n - 1)));
		TupleSet bs = f.range(f.tuple("B0"), f.tuple("B" + (n - 1)));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, as);
		bounds.bound(b, bs);
		bounds.bound(r, a.product(b));
		Formula formula = ((a.eq(a.prime()).not())).and(r.lone()).always();
		Formula run = a.no().eventually();
		
		Solution sol = dsolver.solveAll(formula.and(run), bounds).next();
		
		assertFalse("base problem should not be sat for this trace length", sol.sat());
	}
	
	@Test
	public void testSatSMV() {
		opt.setSolver(SATFactory.electrod("-t", "NuSMV"));
		opt.setRunUnbounded(true);
		opt.setRunTemporal(true);
		dsolver = new PardinusSolver(opt);

		int n = 2;

		Relation a = Relation.unary_variable("a");
		Relation b = Relation.unary("b");
		Relation r = Relation.binary_variable("r");

		Object[] atoms = new Object[n * 2];
		for (int i = 0; i < n; i++)
			atoms[i] = "A" + i;
		for (int i = 0; i < n; i++)
			atoms[n + i] = "B" + i;

		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A" + (n - 1)));
		TupleSet bs = f.range(f.tuple("B0"), f.tuple("B" + (n - 1)));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, as);
		bounds.bound(b, bs);
		bounds.bound(r, a.product(b));
		Formula formula = ((a.eq(a.prime()).not())).and(r.lone()).always();
		Formula run = a.no().eventually();
		
		Solution sol = dsolver.solveAll(formula.and(run), bounds).next();
		
		assertTrue("base problem should be sat", sol.sat());
	}
	
	@Test
	public void testUnsatSMV() {
		opt.setSolver(SATFactory.electrod("-t", "NuSMV"));
		opt.setRunUnbounded(true);
		opt.setRunTemporal(true);
		dsolver = new PardinusSolver(opt);

		int n = 2;

		Relation a = Relation.unary_variable("a");
		Relation b = Relation.unary("b");
		Relation r = Relation.binary_variable("r");

		Object[] atoms = new Object[n * 2];
		for (int i = 0; i < n; i++)
			atoms[i] = "A" + i;
		for (int i = 0; i < n; i++)
			atoms[n + i] = "B" + i;

		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A" + (n - 1)));
		TupleSet bs = f.range(f.tuple("B0"), f.tuple("B" + (n - 1)));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, as);
		bounds.bound(b, bs);
		bounds.bound(r, a.product(b));
		Formula formula = ((a.eq(a.prime()).not())).and(r.some()).always();
		Formula run = r.no().eventually();
		
		Solution sol = dsolver.solveAll(formula.and(run), bounds).next();
		
		assertFalse("base problem should be unsat",sol.sat());
	}
	
	@Test
	public void testSatSMVComplete() {
		opt.setSolver(SATFactory.electrod("-t", "NuSMV"));
		opt.setRunTemporal(true);
		opt.setRunUnbounded(true);
		opt.setMinTraceLength(1);
		opt.setMaxTraceLength(2);
		dsolver = new PardinusSolver(opt);

		int n = 2;

		Relation a = Relation.unary_variable("a");
		Relation b = Relation.unary("b");
		Relation r = Relation.binary_variable("r");

		Object[] atoms = new Object[n * 2];
		for (int i = 0; i < n; i++)
			atoms[i] = "A" + i;
		for (int i = 0; i < n; i++)
			atoms[n + i] = "B" + i;

		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A" + (n - 1)));
		TupleSet bs = f.range(f.tuple("B0"), f.tuple("B" + (n - 1)));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, as);
		bounds.bound(b, bs);
		bounds.bound(r, a.product(b));
		Formula formula = ((a.eq(a.prime()).not())).and(r.lone()).always();
		Formula run = a.no().eventually();
		
		Solution sol = dsolver.solveAll(formula.and(run), bounds).next();
		
		assertTrue("base problem should be sat for this trace length", sol.sat());
	}
	
	@Test
	public void testUnsatSMVLength() {
		opt.setSolver(SATFactory.electrod("-t", "NuSMV"));
		opt.setRunTemporal(true);
		opt.setRunUnbounded(false);
		opt.setMinTraceLength(1);
		opt.setMaxTraceLength(1);
		dsolver = new PardinusSolver(opt);

		int n = 2;

		Relation a = Relation.unary_variable("a");
		Relation b = Relation.unary("b");
		Relation r = Relation.binary_variable("r");

		Object[] atoms = new Object[n * 2];
		for (int i = 0; i < n; i++)
			atoms[i] = "A" + i;
		for (int i = 0; i < n; i++)
			atoms[n + i] = "B" + i;

		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A" + (n - 1)));
		TupleSet bs = f.range(f.tuple("B0"), f.tuple("B" + (n - 1)));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, as);
		bounds.bound(b, bs);
		bounds.bound(r, a.product(b));
		Formula formula = ((a.eq(a.prime()).not())).and(r.lone()).always();
		Formula run = a.no().eventually();
		
		Solution sol = dsolver.solveAll(formula.and(run), bounds).next();
		
		assertFalse("base problem should not be sat for this trace length", sol.sat());
	}
	
	@Test
	public void testTrivial() {
		opt.setSolver(SATFactory.MiniSat);
		opt.setRunTemporal(true);
		opt.setRunUnbounded(false);
		dsolver = new PardinusSolver(opt);

		int n = 2;

		Relation a = Relation.unary_variable("a");
		Relation b = Relation.unary("b");

		Object[] atoms = new Object[n * 2];
		for (int i = 0; i < n; i++)
			atoms[i] = "A" + i;
		for (int i = 0; i < n; i++)
			atoms[n + i] = "B" + i;

		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A" + (n - 1)));
		TupleSet bs = f.range(f.tuple("B0"), f.tuple("B" + (n - 1)));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, as);
		bounds.bound(b, bs);
		
		Solution sol = dsolver.solveAll(Formula.TRUE, bounds).next();
		
		assertNotEquals("temporal problem never trivial", sol.outcome(), Outcome.TRIVIALLY_SATISFIABLE);
	}
	
	@Test
	public void testInvalid1() {
		try {
			opt.setSolver(SATFactory.MiniSat);
			opt.setRunTemporal(false);
			opt.setRunUnbounded(false);
			dsolver = new PardinusSolver(opt);
			int n = 2;

			Relation a = Relation.unary_variable("a");
			Relation b = Relation.unary("b");
			Relation r = Relation.binary_variable("r");

			Object[] atoms = new Object[n * 2];
			for (int i = 0; i < n; i++)
				atoms[i] = "A" + i;
			for (int i = 0; i < n; i++)
				atoms[n + i] = "B" + i;

			Universe uni = new Universe(atoms);
			TupleFactory f = uni.factory();
			TupleSet as = f.range(f.tuple("A0"), f.tuple("A" + (n - 1)));
			TupleSet bs = f.range(f.tuple("B0"), f.tuple("B" + (n - 1)));

			PardinusBounds bounds = new PardinusBounds(uni);
			bounds.bound(a, as);
			bounds.bound(b, bs);
			bounds.bound(r, a.product(b));
			Formula formula = ((a.eq(a.prime()).not())).and(r.some()).always();
			Formula run = r.no().eventually();
			
			dsolver.solveAll(formula.and(run), bounds).next();
			fail("must run temporal for temporal problems");
		} catch (AssertionError e) {}
	}
	
	@Test
	public void testInvalid5() {
		try {
			opt.setSolver(SATFactory.MiniSat);
			opt.setRunTemporal(false);
			opt.setRunUnbounded(false);
			opt.setMaxTraceLength(0);
			dsolver = new PardinusSolver(opt);
			int n = 2;

			Relation a = Relation.unary_variable("a");
			Relation b = Relation.unary("b");
			Relation r = Relation.binary_variable("r");

			Object[] atoms = new Object[n * 2];
			for (int i = 0; i < n; i++)
				atoms[i] = "A" + i;
			for (int i = 0; i < n; i++)
				atoms[n + i] = "B" + i;

			Universe uni = new Universe(atoms);
			TupleFactory f = uni.factory();
			TupleSet as = f.range(f.tuple("A0"), f.tuple("A" + (n - 1)));
			TupleSet bs = f.range(f.tuple("B0"), f.tuple("B" + (n - 1)));

			PardinusBounds bounds = new PardinusBounds(uni);
			bounds.bound(a, as);
			bounds.bound(b, bs);
			bounds.bound(r, a.product(b));
			Formula formula = ((a.eq(a.prime()).not())).and(r.some()).always();
			Formula run = r.no().eventually();
			
			dsolver.solveAll(formula.and(run), bounds).next();
			fail("must run temporal for temporal problems");
		} catch (AssertionError e) {}
	}

	@Test
	public void testInvalid2() {
		try {
			opt.setSolver(SATFactory.electrod("-t", "NuSMV"));
			opt.setRunTemporal(false);
			opt.setRunUnbounded(true);
			dsolver = new PardinusSolver(opt);
			fail("must run temporal for unbounded run");
		} catch (Exception e) {}
	}

	@Test
	public void testInvalid3() {
		try {
			opt.setSolver(SATFactory.electrod("-t", "NuSMV"));
			opt.setRunTemporal(true);
			opt.setRunUnbounded(false);
			dsolver = new PardinusSolver(opt);
			fail("must select bounded solver for bounded run");
		} catch (AssertionError e) {}
	}

	@Test
	public void testInvalid4() {
		try {
			opt.setSolver(SATFactory.MiniSat);
			opt.setRunTemporal(true);
			opt.setRunUnbounded(true);
			dsolver = new PardinusSolver(opt);
			fail("must select complete solver for unbounded run");
		} catch (AssertionError e) {}
	}

	// Regression test, releases bug
	@Test
	public void testBugReleases() {
		opt.setSolver(SATFactory.MiniSat);
		opt.setRunTemporal(true);
		opt.setRunUnbounded(false);
		dsolver = new PardinusSolver(opt);

		int n = 2;

		Relation a = Relation.unary_variable("a");
		Relation b = Relation.unary_variable("b");

		Object[] atoms = new Object[n * 2];
		for (int i = 0; i < n; i++)
			atoms[i] = "A" + i;
		for (int i = 0; i < n; i++)
			atoms[n + i] = "B" + i;

		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A" + (n - 1)));
		TupleSet bs = f.range(f.tuple("B0"), f.tuple("B" + (n - 1)));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, as);
		bounds.bound(b, bs);
		Formula p = a.some();
		Formula q = b.some();
		Formula formula = ((p.releases(q)).after()).iff((p.after()).releases(q.after()));
		
		Solution sol = dsolver.solveAll(formula.not(), bounds).next();
		
		assertFalse("problem should be unsat", sol.sat());
	}
	
	// Regression test, no variable sig bug
	@Test
	public void testBugOnlyStatic() {
		opt.setSolver(SATFactory.MiniSat);
		opt.setRunTemporal(true);
		opt.setRunUnbounded(false);
		dsolver = new PardinusSolver(opt);

		int n = 2;

		Relation a = Relation.unary("a");

		Object[] atoms = new Object[n];
		for (int i = 0; i < n; i++)
			atoms[i] = "A" + i;

		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A" + (n - 1)));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, as);
		Formula p = a.some().always();
		
		Solution sol = dsolver.solveAll(p, bounds).next();
		
		assertTrue("problem should be sat", sol.sat());
	}
}
