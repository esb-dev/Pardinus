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

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Node;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.PardinusSolver;
import kodkod.engine.Solution;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.LinkedHashSet;
import java.util.Map;

import org.junit.BeforeClass;
import org.junit.Test;

/**
 * Tests whether the unsat cores map to the original temporal formula,
 * particularly when skolemization is involved.
 * 
 * @author Nuno Macedo // [HASLab] temporal model finding
 */
public class TemporalUCoreMappingTest {

	private static PardinusSolver dsolver;
	private static ExtendedOptions opt;

	@BeforeClass
	public static void method() throws InterruptedException {
		opt = new ExtendedOptions();
		opt.setSymmetryBreaking(20);
		opt.setRunDecomposed(false);
		opt.setLogTranslation(2);
	}

	@Test
	public void testUnsatGran1() {
		opt.setSolver(SATFactory.MiniSatProver);
		opt.setRunTemporal(true);
		opt.setRunUnbounded(false);
		opt.setCoreGranularity(1);
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
		Formula f10 = (a.eq(a.prime()).not());
		Formula f11 = r.some();
		Formula f1 = f10.and(f11).always();
		Formula f2 = r.no().always();

		Solution sol = dsolver.solveAll(Formula.and(f1,f2), bounds).next();

		assertFalse("base problem should be unsat", sol.sat());
		
		Map<Formula, Node> core = sol.proof().highLevelCore();
		LinkedHashSet<Node> hCore = new LinkedHashSet<Node>(core.keySet());
        hCore.addAll(core.values());

        assertTrue(hCore.contains(f1));
        assertTrue(hCore.contains(f2));
        assertFalse(hCore.contains(f10));
        assertFalse(hCore.contains(f11));
        
        System.out.println(hCore);
	}
	
	@Test
	public void testUnsatGran2() {
		opt.setSolver(SATFactory.MiniSatProver);
		opt.setRunTemporal(true);
		opt.setRunUnbounded(false);
		opt.setCoreGranularity(2);
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
		Formula f10 = (a.eq(a.prime()).not());
		Formula f11 = r.some();
		Formula f1 = f10.and(f11).always();
		Formula f2 = r.no().always();

		Solution sol = dsolver.solveAll(Formula.and(f1,f2), bounds).next();

		assertFalse("base problem should be unsat", sol.sat());
		
		Map<Formula, Node> core = sol.proof().highLevelCore();
		LinkedHashSet<Node> hCore = new LinkedHashSet<Node>(core.keySet());
        hCore.addAll(core.values());

        assertTrue(hCore.contains(f1));
        assertTrue(hCore.contains(f2));
        assertFalse(hCore.contains(f10));
        assertFalse(hCore.contains(f11));
        
        System.out.println(hCore);
	}
	
	@Test
	public void testUnsatGran3() {
		opt.setSolver(SATFactory.MiniSatProver);
		opt.setRunTemporal(true);
		opt.setRunUnbounded(false);
		opt.setCoreGranularity(3);
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
		Formula f10 = (a.eq(a.prime()).not());
		Formula f11 = r.some();
		Formula f1 = f10.and(f11).always();
		Formula f2 = r.no().always();

		Solution sol = dsolver.solveAll(Formula.and(f1,f2), bounds).next();

		assertFalse("base problem should be unsat", sol.sat());
		
		Map<Formula, Node> core = sol.proof().highLevelCore();
		LinkedHashSet<Node> hCore = new LinkedHashSet<Node>(core.keySet());
        hCore.addAll(core.values());

        assertFalse(hCore.contains(f1));
        assertTrue(hCore.contains(f2));
        assertFalse(hCore.contains(f10));
        assertTrue(hCore.contains(f11));
        
        System.out.println(hCore);
	}

	@Test
	public void testUnsatGran1Skolem() {
		opt.setSolver(SATFactory.MiniSatProver);
		opt.setRunTemporal(true);
		opt.setRunUnbounded(false);
		opt.setCoreGranularity(1);
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
		Formula f10 = (a.eq(a.prime()).not());
		Formula f11 = r.eq(Expression.UNIV.product(b));
		Formula f1 = f10.and(f11).always();
		Variable x = Variable.unary("x");
		Formula f20 = (x.product(b)).in(r.prime()).not();
		Formula f2 = f20.forSome(x.oneOf(a));

		Solution sol = dsolver.solveAll(Formula.and(f1,f2), bounds).next();

		assertFalse("base problem should be unsat", sol.sat());
		
		Map<Formula, Node> core = sol.proof().highLevelCore();
		LinkedHashSet<Node> hCore = new LinkedHashSet<Node>(core.keySet());
        hCore.addAll(core.values());

        assertTrue(hCore.contains(f1));
        assertTrue(hCore.contains(f2));
        assertFalse(hCore.contains(f10));
        assertFalse(hCore.contains(f11));
        assertFalse(hCore.contains(f20));
        
        System.out.println(hCore);
	}
	
	@Test
	public void testUnsatGran2Skolem() {
		opt.setSolver(SATFactory.MiniSatProver);
		opt.setRunTemporal(true);
		opt.setRunUnbounded(false);
		opt.setCoreGranularity(2);
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
		Formula f10 = (a.eq(a.prime()).not());
		Formula f11 = r.eq(Expression.UNIV.product(b));
		Formula f1 = f10.and(f11).always();
		Variable x = Variable.unary("x");
		Formula f20 = (x.product(b)).in(r.prime()).not();
		Formula f2 = f20.forSome(x.oneOf(a));

		Solution sol = dsolver.solveAll(Formula.and(f1,f2), bounds).next();

		assertFalse("base problem should be unsat", sol.sat());
		
		Map<Formula, Node> core = sol.proof().highLevelCore();
		LinkedHashSet<Node> hCore = new LinkedHashSet<Node>(core.keySet());
        hCore.addAll(core.values());

        assertTrue(hCore.contains(f1));
        assertFalse(hCore.contains(f2));
        assertFalse(hCore.contains(f10));
        assertFalse(hCore.contains(f11));
        assertTrue(hCore.contains(f20));
        
        System.out.println(hCore);
	}
	
	
	@Test
	public void testUnsatGran3Skolem() {
		opt.setSolver(SATFactory.MiniSatProver);
		opt.setRunTemporal(true);
		opt.setRunUnbounded(false);
		opt.setCoreGranularity(3);
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
		Formula f10 = (a.eq(a.prime()).not());
		Formula f11 = r.eq(Expression.UNIV.product(b));
		Formula f1 = f10.and(f11).always();
		Variable x = Variable.unary("x");
		Formula f20 = (x.product(b)).in(r.prime()).not();
		Formula f2 = f20.forSome(x.oneOf(a));

		Solution sol = dsolver.solveAll(Formula.and(f1,f2), bounds).next();

		assertFalse("base problem should be unsat", sol.sat());
		
		Map<Formula, Node> core = sol.proof().highLevelCore();
		LinkedHashSet<Node> hCore = new LinkedHashSet<Node>(core.keySet());
        hCore.addAll(core.values());

        assertFalse(hCore.contains(f1));
        assertFalse(hCore.contains(f2));
        assertFalse(hCore.contains(f10));
        assertTrue(hCore.contains(f11));
        assertTrue(hCore.contains(f20));
        
        System.out.println(hCore);
	}
	
	@Test
	public void testUnsatGran1SkolemTrivial() {
		opt.setSolver(SATFactory.MiniSatProver);
		opt.setRunTemporal(true);
		opt.setRunUnbounded(false);
		opt.setCoreGranularity(1);
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
		Formula f10 = (a.eq(a.prime()).not());
		Formula f11 = r.eq(Expression.UNIV.product(Expression.UNIV));
		Formula f1 = f10.and(f11).always();
		Variable x = Variable.unary("x");
		Formula f2 = (x.product(b)).in(r.prime()).not().forSome(x.oneOf(a));

		Solution sol = dsolver.solveAll(Formula.and(f1,f2), bounds).next();

		assertFalse("base problem should be unsat", sol.sat());
		
		Map<Formula, Node> core = sol.proof().highLevelCore();
		LinkedHashSet<Node> hCore = new LinkedHashSet<Node>(core.keySet());
        hCore.addAll(core.values());

        assertTrue(hCore.contains(f1));
        assertTrue(hCore.contains(f2));
        assertFalse(hCore.contains(f10));
        assertFalse(hCore.contains(f11));
        
        System.out.println(hCore);
	}

}
