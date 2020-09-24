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

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.util.Iterator;

import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.Evaluator;
import kodkod.engine.Explorer;
import kodkod.engine.PardinusSolver;
import kodkod.engine.Solution;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Instance;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TemporalInstance;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;
import org.junit.Test;

/**
 * Tests whether the representation of {@link TemporalInstance temporal
 * instances} as sequences of states and as an extended static model is
 * consistent.
 * 
 * @author Nuno Macedo // [HASLab] temporal model finding
 */
public class InstanceExpansionTests {

	@Test
	public void testTmp1SMV() {
		int n = 3;

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
		bounds.bound(r, as.product(bs));
		Formula formula = ((a.eq(a.prime()).not())).and(r.some()).always();

		ExtendedOptions opt = new ExtendedOptions();

//		opt.setReporter(new SLF4JReporter());
		opt.setRunTemporal(true);
		opt.setRunUnbounded(true);
		opt.setRunDecomposed(false);
		opt.setSolver(SATFactory.electrod("-t", "NuSMV"));
		PardinusSolver solver = new PardinusSolver(opt);

		Iterator<Solution> solution = solver.solveAll(formula, bounds);
		TemporalInstance inst = (TemporalInstance) solution.next().instance();
		Evaluator e1 = new Evaluator(inst);
		for (int i = 0; i < inst.prefixLength() + 3; i++) {
			Evaluator e2 = new Evaluator(inst.state(i));
			assertEquals("expanded representation mistached with single state", e1.evaluate(a, i).toString(), e2.evaluate(a).toString());
			assertEquals("expanded representation mistached with single state", e1.evaluate(b, i).toString(), e2.evaluate(b).toString());
		}

//		inst = (TemporalInstance) solution.next().instance();
//		e1 = new Evaluator(inst);
//		for (int i = 0; i < inst.prefixLength() + 3; i++) {
//			Evaluator e2 = new Evaluator(inst.state(i));
//			assertEquals("expanded representation mistached with single state", e1.evaluate(a, i).toString(), e2.evaluate(a).toString());
//			assertEquals("expanded representation mistached with single state", e1.evaluate(b, i).toString(), e2.evaluate(b).toString());
//		}
//
//		assertTrue("formula should hold", e1.evaluate(((a.eq(a.prime()).not())).always(),0));
//		assertFalse("formula should not hold", e1.evaluate(((a.eq(a.prime()))).always(),0));

		solver.free();
	}

	@Test
	public void testTmp2SMV() {
		int n = 3;

		Relation a = Relation.unary_variable("a");
		Relation b = Relation.unary_variable("b");
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
		Formula formula = ((a.eq(a.prime()).not()).and((b.eq(b.prime().prime()).not()))).always();

		ExtendedOptions opt = new ExtendedOptions();

//		opt.setReporter(new SLF4JReporter());
		opt.setRunTemporal(true);
		opt.setRunUnbounded(true);
		opt.setRunDecomposed(false);
		opt.setSolver(SATFactory.electrod("-t", "NuSMV"));
		PardinusSolver solver = new PardinusSolver(opt);

		Iterator<Solution> solution = solver.solveAll(formula, bounds);
		TemporalInstance inst = (TemporalInstance) solution.next().instance();
		Evaluator e1 = new Evaluator(inst);
		for (int i = 0; i < inst.prefixLength() + 3; i++) {
			Evaluator e2 = new Evaluator(inst.state(i));
			assertEquals("expanded representation mistached with single state", e1.evaluate(a, i).toString(), e2.evaluate(a).toString());
			assertEquals("expanded representation mistached with single state", e1.evaluate(b, i).toString(), e2.evaluate(b).toString());
		}

//		inst = (TemporalInstance) solution.next().instance();
//		e1 = new Evaluator(inst);
//		for (int i = 0; i < inst.prefixLength() + 3; i++) {
//			Evaluator e2 = new Evaluator(inst.state(i));
//			assertEquals("expanded representation mistached with single state", e1.evaluate(a, i).toString(), e2.evaluate(a).toString());
//			assertEquals("expanded representation mistached with single state", e1.evaluate(b, i).toString(), e2.evaluate(b).toString());
//		}
//
//		assertTrue("formula should hold", e1.evaluate(((a.eq(a.prime()).not())).always(),0));
//		assertFalse("formula should not hold", e1.evaluate(((a.eq(a.prime()))).always(),0));

		solver.free();
	}

	@Test
	public void testTmp3SMV() {
		int n = 3;

		Relation a = Relation.unary_variable("a");
		Relation r = Relation.binary_variable("r");

		Object[] atoms = new Object[n];
		for (int i = 0; i < n; i++)
			atoms[i] = "A" + i;

		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A" + (n - 1)));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, as);
		bounds.bound(r, as.product(as));
		Formula formula = ((a.eq(a.prime()).not()).and(r.some())).always();

		ExtendedOptions opt = new ExtendedOptions();

//		opt.setReporter(new SLF4JReporter());
		opt.setRunTemporal(true);
		opt.setRunUnbounded(true);
		opt.setRunDecomposed(false);
		opt.setSolver(SATFactory.electrod("-t", "NuSMV"));
		PardinusSolver solver = new PardinusSolver(opt);

		Iterator<Solution> solution = solver.solveAll(formula, bounds);
		TemporalInstance inst = (TemporalInstance) solution.next().instance();
		Evaluator e1 = new Evaluator(inst);
		for (int i = 0; i < inst.prefixLength() + 3; i++) {
			Evaluator e2 = new Evaluator(inst.state(i));
			assertEquals("expanded representation mistached with single state", e1.evaluate(a, i).toString(), e2.evaluate(a).toString());
			assertEquals("expanded representation mistached with single state", e1.evaluate(r, i).toString(), e2.evaluate(r).toString());
		}

//		inst = (TemporalInstance) solution.next().instance();
//		e1 = new Evaluator(inst);
//		for (int i = 0; i < inst.prefixLength() + 3; i++) {
//			Evaluator e2 = new Evaluator(inst.state(i));
//			assertEquals("expanded representation mistached with single state", e1.evaluate(a, i).toString(), e2.evaluate(a).toString());
//			assertEquals("expanded representation mistached with single state", e1.evaluate(r, i).toString(), e2.evaluate(r).toString());
//		}
//
//		assertTrue("formula should hold", e1.evaluate(((a.eq(a.prime()).not())).always(),0));
//		assertFalse("formula should not hold", e1.evaluate(((a.eq(a.prime()))).always(),0));

		solver.free();
	}

	@Test
	public void testTmp3SAT() {
		int n = 3;

		Relation a = Relation.unary_variable("a");
		Relation r = Relation.binary_variable("r");
		Relation s = Relation.binary_variable("s");

		Object[] atoms = new Object[n];
		for (int i = 0; i < n; i++)
			atoms[i] = "A" + i;

		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A" + (n - 1)));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, as);
		bounds.bound(r, as.product(as));
		bounds.bound(s, a.product(a));
		Formula formula = ((a.eq(a.prime()).not()).and(r.some())).always();

		ExtendedOptions opt = new ExtendedOptions();

//		opt.setReporter(new SLF4JReporter());
		opt.setRunTemporal(true);
		opt.setRunUnbounded(false);
		opt.setRunDecomposed(false);
		opt.setMaxTraceLength(10);
		opt.setSolver(SATFactory.MiniSat);
		PardinusSolver solver = new PardinusSolver(opt);

		Iterator<Solution> solution = solver.solveAll(formula, bounds);
		TemporalInstance inst = (TemporalInstance) solution.next().instance();
		Evaluator e1 = new Evaluator(inst);
		for (int i = 0; i < inst.prefixLength(); i++) {
			Evaluator e2 = new Evaluator(inst.state(i));
			assertEquals("expanded representation mistached with single state", e1.evaluate(a, i).toString(), e2.evaluate(a).toString());
			assertEquals("expanded representation mistached with single state", e1.evaluate(r, i).toString(), e2.evaluate(r).toString());
		}

		inst = (TemporalInstance) solution.next().instance();
		e1 = new Evaluator(inst);
		for (int i = 0; i < inst.prefixLength(); i++) {
			Evaluator e2 = new Evaluator(inst.state(i));
			assertEquals("expanded representation mistached with single state", e1.evaluate(a, i).toString(), e2.evaluate(a).toString());
			assertEquals("expanded representation mistached with single state", e1.evaluate(r, i).toString(), e2.evaluate(r).toString());
		}

		assertTrue("formula should hold", e1.evaluate(((a.eq(a.prime()).not())).always(),0));
		assertFalse("formula should not hold", e1.evaluate(((a.eq(a.prime()))).always(),0));

		solver.free();
	}
	
	@Test
	public void testTmp4SAT() {
		int n = 3;

		Relation a = Relation.unary_variable("a");

		Object[] atoms = new Object[n];
		for (int i = 0; i < n; i++)
			atoms[i] = "A" + i;

		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A" + (n - 1)));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, as);
		Formula formula = Formula.and(a.no(),a.eq(a.prime()).not().always());

		ExtendedOptions opt = new ExtendedOptions();

//		opt.setReporter(new SLF4JReporter());
		opt.setRunTemporal(true);
		opt.setRunUnbounded(false);
		opt.setRunDecomposed(false);
		opt.setMaxTraceLength(10);
		opt.setSolver(SATFactory.MiniSat);
		PardinusSolver solver = new PardinusSolver(opt);

		Iterator<Solution> solution = solver.solveAll(formula, bounds);
		TemporalInstance inst = (TemporalInstance) solution.next().instance();
		Evaluator e1 = new Evaluator(inst);
		for (int i = 0; i < inst.prefixLength(); i++) {
			Evaluator e2 = new Evaluator(inst.state(i));
			assertEquals("expanded representation mistached with single state", e1.evaluate(a, i).toString(), e2.evaluate(a).toString());
			e2 = new Evaluator(inst.state(i+1));
			assertEquals("expanded representation mistached with single state", e1.evaluate(a.prime(), i).toString(), e2.evaluate(a).toString());
		}

		inst = (TemporalInstance) solution.next().instance();
		e1 = new Evaluator(inst);
		for (int i = 0; i < inst.prefixLength(); i++) {
			Evaluator e2 = new Evaluator(inst.state(i));
			assertEquals("expanded representation mistached with single state", e1.evaluate(a, i).toString(), e2.evaluate(a).toString());
			e2 = new Evaluator(inst.state(i+1));
			assertEquals("expanded representation mistached with single state", e1.evaluate(a.prime(), i).toString(), e2.evaluate(a).toString());
		}

		assertFalse("formula should not hold", e1.evaluate(a.some().before().once(),0));
		assertFalse("formula should not hold", e1.evaluate(a.some().before().once().after(),0));
		assertFalse("formula should not hold", e1.evaluate(a.some().before().once(),1));
		assertTrue("formula should hold", e1.evaluate(a.some().before().once().after(),1));
		assertTrue("formula should hold", e1.evaluate(a.some().before().once().after().after(),0));
		assertTrue("formula should hold", e1.evaluate(a.some().before().once().eventually(),0));

		solver.free();
	}

	@Test
	public void testSta1SAT() {
		int n = 3;

		Relation a = Relation.unary("a");
		Relation b = Relation.unary("b");
		Relation r = Relation.binary("r");

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
		Formula formula = r.some();

		ExtendedOptions opt = new ExtendedOptions();

//		opt.setReporter(new SLF4JReporter());
		opt.setRunTemporal(false);
		opt.setRunUnbounded(false);
		opt.setRunDecomposed(false);
		opt.setSolver(SATFactory.MiniSat);
		PardinusSolver solver = new PardinusSolver(opt);

		Iterator<Solution> solution = solver.solveAll(formula, bounds);
		Instance inst = solution.next().instance();
		Evaluator e1 = new Evaluator(inst);

		e1.evaluate(a).toString();

		try {
			e1.evaluate(a, 0).toString();
			fail("should not eval static instances");
		} catch (IllegalArgumentException e) {}

		solver.free();
	}
	
	@Test
	public void testSta2SAT() {
		int n = 3;

		Relation a = Relation.unary("a");
		Relation b = Relation.unary("b");
		Relation r = Relation.binary("r");

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
		Formula formula = r.some();

		ExtendedOptions opt = new ExtendedOptions();

//		opt.setReporter(new SLF4JReporter());
		opt.setRunTemporal(true);
		opt.setRunUnbounded(false);
		opt.setRunDecomposed(false);
		opt.setSolver(SATFactory.MiniSat);
		PardinusSolver solver = new PardinusSolver(opt);

		Explorer<Solution> solution = solver.solveAll(formula, bounds);
		TemporalInstance inst = (TemporalInstance) solution.nextC().instance();
		Evaluator e1 = new Evaluator(inst);
		for (int i = 0; i < inst.prefixLength() + 3; i++) {
			Evaluator e2 = new Evaluator(inst.state(i));
			assertEquals("expanded representation mistached with single state", e1.evaluate(a, i).toString(), e2.evaluate(a).toString());
			assertEquals("expanded representation mistached with single state", e1.evaluate(r, i).toString(), e2.evaluate(r).toString());
		}

		inst = (TemporalInstance) solution.nextC().instance();
		e1 = new Evaluator(inst);
		for (int i = 0; i < inst.prefixLength() + 2; i++) {
			Evaluator e2 = new Evaluator(inst.state(i));
			assertEquals("expanded representation mistached with single state", e1.evaluate(a, i).toString(), e2.evaluate(a).toString());
			assertEquals("expanded representation mistached with single state", e1.evaluate(r, i).toString(), e2.evaluate(r).toString());
		}

		assertTrue("formula should hold", e1.evaluate(((a.eq(a.prime()))).always(),0));
		assertFalse("formula should not hold", e1.evaluate(((a.eq(a.prime()).not())).always(),0));

		solver.free();
	}
}
