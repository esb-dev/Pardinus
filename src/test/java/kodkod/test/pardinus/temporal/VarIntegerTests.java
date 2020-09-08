package kodkod.test.pardinus.temporal;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.Iterator;

import org.junit.Test;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.IntConstant;
import kodkod.ast.Relation;
import kodkod.engine.Evaluator;
import kodkod.engine.PardinusSolver;
import kodkod.engine.Solution;
import kodkod.engine.config.ExtendedOptions;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

/**
 * Tests for mutable integer relations.
 *
 * @author Nuno Macedo // [HASLab] temporal model finding
 */
public class VarIntegerTests {

	@Test
	public void test0() {
		Relation a = Relation.unary_variable("a");
		
        Universe uni = new Universe("-2", "-1", "0", "1");
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("-2"), f.tuple("1"));

		PardinusBounds bounds = new PardinusBounds(uni);

		bounds.boundExactly(-2, f.range(f.tuple("-2"), f.tuple("-2")));
		bounds.boundExactly(-1, f.range(f.tuple("-1"), f.tuple("-1")));
		bounds.boundExactly(0, f.range(f.tuple("0"), f.tuple("0")));
		bounds.boundExactly(1, f.range(f.tuple("1"), f.tuple("1")));

		bounds.bound(a, as);
		Formula formula = a.sum().eq(IntConstant.constant(1)).always();
        
		ExtendedOptions opt = new ExtendedOptions();
//		opt.setReporter(new SLF4JReporter());
        opt.setBitwidth(2);
		opt.setRunTemporal(true);
		opt.setRunDecomposed(false);
		opt.setMaxTraceLength(2);
		opt.setNoOverflow(false);
		PardinusSolver solver = new PardinusSolver(opt);
		
		assertTrue("expected sat", solver.solve(formula, bounds).sat());

		Iterator<Solution> sols = solver.solveAll(formula, bounds);
		Solution sol = sols.next();
		int c = 1;
		while (sol.sat()) {
			sol = sols.next();
			c++;
			if (sol.sat()) {
				opt.reporter().debug(sol.instance().toString());
			}
		}
		assertEquals(29, c);
		
		solver.free();

	}
	
	@Test
	public void test1() {
		Relation a = Relation.unary_variable("a");
		
        Universe uni = new Universe("-2", "-1", "0", "1");
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("-2"), f.tuple("1"));

		PardinusBounds bounds = new PardinusBounds(uni);

		bounds.boundExactly(-2, f.range(f.tuple("-2"), f.tuple("-2")));
		bounds.boundExactly(-1, f.range(f.tuple("-1"), f.tuple("-1")));
		bounds.boundExactly(0, f.range(f.tuple("0"), f.tuple("0")));
		bounds.boundExactly(1, f.range(f.tuple("1"), f.tuple("1")));

		bounds.bound(a, as);
		Formula formula = (a.sum().eq(IntConstant.constant(1)).and(a.count().eq(IntConstant.constant(-2)))).always();
        
		ExtendedOptions opt = new ExtendedOptions();
        opt.setBitwidth(2);
		opt.setRunTemporal(true);
		opt.setRunDecomposed(false);
		opt.setMaxTraceLength(2);
		opt.setNoOverflow(false);
		PardinusSolver solver = new PardinusSolver(opt);
		
		assertTrue("expected sat", solver.solve(formula, bounds).sat());

		Iterator<Solution> sols = solver.solveAll(formula, bounds);
		Solution sol = sols.next();
		
		int c = 1;
		while (sol.sat()) {
			sol = sols.next();
			c++;
			if (sol.sat()) {
				opt.reporter().debug(sol.instance().toString());
			}
		}
		assertEquals(7, c);
		solver.free();

	}
	
	@Test
	public void testU() {
		Relation a = Relation.unary_variable("a");
		
        Universe uni = new Universe("-2", "-1", "0", "1");
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("-2"), f.tuple("1"));

		PardinusBounds bounds = new PardinusBounds(uni);

		bounds.boundExactly(-2, f.range(f.tuple("-2"), f.tuple("-2")));
		bounds.boundExactly(-1, f.range(f.tuple("-1"), f.tuple("-1")));
		bounds.boundExactly(0, f.range(f.tuple("0"), f.tuple("0")));
		bounds.boundExactly(1, f.range(f.tuple("1"), f.tuple("1")));

		bounds.bound(a, as);
		Formula formula = a.sum().eq(IntConstant.constant(2)).always();
        
		ExtendedOptions opt = new ExtendedOptions();
        opt.setBitwidth(2);
		opt.setRunTemporal(true);
		opt.setRunDecomposed(false);
		opt.setMaxTraceLength(3);
		opt.setNoOverflow(true);
//		opt.setReporter(new ConsoleReporter());
		PardinusSolver solver = new PardinusSolver(opt);
		
		assertFalse("expected unsat", solver.solve(formula, bounds).sat());
	}
	
	@Test
	public void testEnc() {
		Relation a = Relation.unary_variable("a");
		
        Universe uni = new Universe("-2", "-1", "0", "1");
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("-2"), f.tuple("1"));

		PardinusBounds bounds = new PardinusBounds(uni);

		bounds.boundExactly(-2, f.range(f.tuple("-2"), f.tuple("-2")));
		bounds.boundExactly(-1, f.range(f.tuple("-1"), f.tuple("-1")));
		bounds.boundExactly(0, f.range(f.tuple("0"), f.tuple("0")));
		bounds.boundExactly(1, f.range(f.tuple("1"), f.tuple("1")));

		bounds.bound(a, as);
		Formula formula = a.sum().eq(IntConstant.constant(1)).always();
        
		ExtendedOptions opt = new ExtendedOptions();
//		opt.setReporter(new SLF4JReporter());
        opt.setBitwidth(2);
		opt.setRunTemporal(true);
		opt.setRunDecomposed(false);
		opt.setMaxTraceLength(2);
		opt.setNoOverflow(false);
		PardinusSolver solver = new PardinusSolver(opt);
		
		assertTrue("expected sat", solver.solve(formula, bounds).sat());

		Solution sol = solver.solveAll(formula, bounds).next();

		assertEquals(4,sol.instance().ints().size());

		Evaluator eval = new Evaluator(sol.instance());

		assertEquals(4,eval.evaluate(Expression.INTS).size());
		assertEquals(4,eval.evaluate(Expression.INTS,2).size());

		assertEquals(2,eval.evaluate(a).size());
		assertEquals(2,eval.evaluate(a,3).size());

		solver.free();

	}

}
