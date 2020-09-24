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
package kodkod.test.pardinus;

import static org.junit.Assert.assertEquals;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.config.ExtendedOptions;
import kodkod.instance.Instance;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TemporalInstance;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;
import org.junit.Test;

/**
 * Tests the reification of state and path instances into formulas, needed for
 * non-incremental iteration.
 * 
 * @author Nuno Macedo // [HASLab] temporal model finding
 */
public class ReificationTests {
	
	/* Static reification. */
	@Test
	public void testStaticReif() {
		int n = 3;

		Relation a = Relation.unary("a");
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
		Formula formula = a.some().and(b.some());

		ExtendedOptions opt = new ExtendedOptions();

		Map<Object, Expression> x = new HashMap<Object, Expression>();

		Instance inst = new Instance(uni);
		inst.add(a, f.setOf("A"+(n-1)));
		inst.add(b, f.setOf("B"+(n-1)));
		
		opt.reporter().debug(inst.toString());
//		relations: {a=[[A2]], b=[[B2]]}

		assertEquals("((a = $$A2$$) and (b = $$B2$$))", inst.formulate(x, formula, false, bounds.clone()).toString());

		formula = formula.and(inst.formulate(x, formula, false, bounds).not());

		inst = new Instance(uni);
		inst.add(a, f.range(f.tuple("A1"),f.tuple("A2")));
		inst.add(b, f.range(f.tuple("B1"),f.tuple("B2")));

		opt.reporter().debug(inst.toString());

//		relations: {a=[[A1], [A2]], b=[[B1], [B2]], $$A2$$=[[A2]], $$B2$$=[[B2]], $$A0$$=[[A0]], $$A1$$=[[A1]], $$B0$$=[[B0]], $$B1$$=[[B1]]}

		assertEquals("((a = ($$A1$$ + $$A2$$)) and (b = ($$B1$$ + $$B2$$)))",
				inst.formulate(x, formula, false, bounds.clone()).toString());

		formula = formula.and(inst.formulate(x, formula, false, bounds).not());

		inst = new Instance(uni);
		inst.add(a, f.range(f.tuple("A1"),f.tuple("A2")));
		inst.add(b, f.setOf("B"+(n-1)));

		opt.reporter().debug(inst.toString());

//		relations: {a=[[A1], [A2]], b=[[B2]], $$A1$$=[[A1]], $$A2$$=[[A2]], $$B1$$=[[B1]], $$B2$$=[[B2]], $$A0$$=[[A0]], $$B0$$=[[B0]]}

		assertEquals("((a = ($$A1$$ + $$A2$$)) and (b = $$B2$$))",
				inst.formulate(x, formula, false, bounds.clone()).toString());

	}

	/* Temporal reification, not all relations relevant, loop not first. */
	@Test
	public void testTmpReif() {
		int n = 3;

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
		Formula formula = ((a.eq(a.prime()).not())).always();

		ExtendedOptions opt = new ExtendedOptions();
//		opt.setReporter(new ConsoleReporter());

		Map<Object, Expression> x = new HashMap<Object, Expression>();

		Instance inst0 = new Instance(uni);
		inst0.add(a, f.noneOf(1));
		inst0.add(b, f.noneOf(1));
		Instance inst1 = new Instance(uni);
		inst1.add(a, f.range(f.tuple("A0"), f.tuple("A" + (n - 1))));
		inst1.add(b, f.noneOf(1));
		TemporalInstance inst = new TemporalInstance(Arrays.asList(inst0, inst1), 0, 1);
		
		opt.reporter().debug(inst.toString());

//		* state 0 LOOP
//		relations: {a=[], b=[]}
//		* state 1 LAST
//		relations: {a=[[A0], [A1], [A2]], b=[]}

		assertEquals(
				"(((a = none) and after((a = (($$A0$$ + $$A1$$) + $$A2$$)))) and always((((a = none) implies after(after((a = none)))) and ((a = (($$A0$$ + $$A1$$) + $$A2$$)) implies after(after((a = (($$A0$$ + $$A1$$) + $$A2$$))))))))",
				inst.formulate(x, formula, false, bounds.clone()).toString());

		inst0 = new Instance(uni);
		inst0.add(a, f.setOf("A"+(n-1)));
		inst0.add(b, f.noneOf(1));
		inst1 = new Instance(uni);
		inst1.add(a, f.range(f.tuple("A0"), f.tuple("A1")));
		inst1.add(b, f.noneOf(1));
		inst = new TemporalInstance(Arrays.asList(inst0, inst1), 0, 1);

		opt.reporter().debug(inst.toString());

//		* state 0 LOOP
//		relations: {a=[[A2]], b=[]}
//		* state 1 LAST
//		relations: {a=[[A0], [A1]], b=[]}

		assertEquals(
				"(((a = $$A2$$) and after((a = ($$A0$$ + $$A1$$)))) and always((((a = $$A2$$) implies after(after((a = $$A2$$)))) and ((a = ($$A0$$ + $$A1$$)) implies after(after((a = ($$A0$$ + $$A1$$))))))))",
				inst.formulate(x, formula, false, bounds.clone()).toString());
	}

	/* Temporal reification. */
	@Test
	public void testTmp2Reif() {
		int n = 3;

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
		Formula formula = ((a.eq(a.prime()).not())).always().and(b.no().and(b.some().always().after()));

		ExtendedOptions opt = new ExtendedOptions();

//		opt.setReporter(new SLF4JReporter());

		Map<Object, Expression> x = new HashMap<Object, Expression>();

		Instance inst0 = new Instance(uni);
		inst0.add(a, f.setOf("A1","A2"));
		inst0.add(b, f.noneOf(1));
		Instance inst1 = new Instance(uni);
		inst1.add(a, f.setOf("A0","A2"));
		inst1.add(b, f.setOf("B2"));
		Instance inst2 = new Instance(uni);
		inst2.add(a, f.setOf("A1"));
		inst2.add(b, f.setOf("B1"));
		TemporalInstance inst = new TemporalInstance(Arrays.asList(inst0, inst1, inst2), 1, 1);

		opt.reporter().debug(inst.toString());

//		* state 0
//		relations: {a=[[A1], [A2]], b=[]}
//		* state 1 LOOP
//		relations: {a=[[A0], [A2]], b=[[B2]]}
//		* state 2 LAST
//		relations: {a=[[A1]], b=[[B1]]}

		assertEquals(
				"((((a = ($$A1$$ + $$A2$$)) and (b = none)) and after((((a = ($$A0$$ + $$A2$$)) and (b = $$B2$$)) and after(((a = $$A1$$) and (b = $$B1$$)))))) and after(always(((((a = ($$A0$$ + $$A2$$)) and (b = $$B2$$)) implies after(after(((a = ($$A0$$ + $$A2$$)) and (b = $$B2$$))))) and (((a = $$A1$$) and (b = $$B1$$)) implies after(after(((a = $$A1$$) and (b = $$B1$$)))))))))",
				inst.formulate(x, formula, false, bounds.clone()).toString());

		inst0 = new Instance(uni);
		inst0.add(a, f.setOf("A2"));
		inst0.add(b, f.noneOf(1));
		inst1 = new Instance(uni);
		inst1.add(a, f.setOf("A1"));
		inst1.add(b, f.setOf("B2"));
		inst2 = new Instance(uni);
		inst2.add(a, f.setOf("A0","A2"));
		inst2.add(b, f.setOf("B1"));
		inst = new TemporalInstance(Arrays.asList(inst0, inst1, inst2), 1, 1);
		
		opt.reporter().debug(inst.toString());

//		* state 0
//		relations: {a=[[A2]], b=[]}
//		* state 1 LOOP
//		relations: {a=[[A1]], b=[[B2]]}
//		* state 2 LAST
//		relations: {a=[[A0], [A2]], b=[[B1]]}

		assertEquals(
				"((((a = $$A2$$) and (b = none)) and after((((a = $$A1$$) and (b = $$B2$$)) and after(((a = ($$A0$$ + $$A2$$)) and (b = $$B1$$)))))) and after(always(((((a = $$A1$$) and (b = $$B2$$)) implies after(after(((a = $$A1$$) and (b = $$B2$$))))) and (((a = ($$A0$$ + $$A2$$)) and (b = $$B1$$)) implies after(after(((a = ($$A0$$ + $$A2$$)) and (b = $$B1$$)))))))))",
				inst.formulate(x, formula, false, bounds.clone()).toString());

	}

	/* Temporal segment reification. */
	@Test
	public void testTmpSegmentReif() {
		int n = 3;

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
		Formula formula = ((a.eq(a.prime()).not())).always().and(b.no().and(b.some().always().after()));

		ExtendedOptions opt = new ExtendedOptions();

//		opt.setReporter(new ConsoleReporter());

		Map<Object, Expression> x = new HashMap<Object, Expression>();

		Instance inst0 = new Instance(uni);
		inst0.add(a, f.setOf("A1","A2"));
		inst0.add(b, f.noneOf(1));
		Instance inst1 = new Instance(uni);
		inst1.add(a, f.setOf("A0","A2"));
		inst1.add(b, f.setOf("B2"));
		Instance inst2 = new Instance(uni);
		inst2.add(a, f.setOf("A1"));
		inst2.add(b, f.setOf("B1"));
		TemporalInstance inst = new TemporalInstance(Arrays.asList(inst0, inst1, inst2), 1, 1);

		opt.reporter().debug(inst.toString());

//		* state 0
//		relations: {a=[[A1], [A2]], b=[]}
//		* state 1 LOOP
//		relations: {a=[[A0], [A2]], b=[[B2]]}
//		* state 2 LAST
//		relations: {a=[[A1]], b=[[B1]]}

		assertEquals("true", inst.formulate(bounds.clone(), x, formula, -1, -1, false).toString());

		assertEquals(
				"after((((a = ($$A0$$ + $$A2$$)) and (b = $$B2$$)) and after(((a = $$A1$$) and (b = $$B1$$)))))",
				inst.formulate(bounds.clone(), x, formula, 1, 2, false).toString());

		assertEquals(
				"(after(after((((a = $$A1$$) and (b = $$B1$$)) and after(((a = ($$A0$$ + $$A2$$)) and (b = $$B2$$)))))) and after(always(((((a = ($$A0$$ + $$A2$$)) and (b = $$B2$$)) implies after(after(((a = ($$A0$$ + $$A2$$)) and (b = $$B2$$))))) and (((a = $$A1$$) and (b = $$B1$$)) implies after(after(((a = $$A1$$) and (b = $$B1$$)))))))))",
				inst.formulate(bounds.clone(), x, formula, 2, null, false).toString());

		assertEquals(
				"(((a = ($$A1$$ + $$A2$$)) and (b = none)) and after((((a = ($$A0$$ + $$A2$$)) and (b = $$B2$$)) and after(((a = $$A1$$) and (b = $$B1$$))))))",
				inst.formulate(bounds.clone(), x, formula, 0, 2, false).toString());

		assertEquals(
				"(((a = ($$A1$$ + $$A2$$)) and (b = none)) and after((((a = ($$A0$$ + $$A2$$)) and (b = $$B2$$)) and after(((a = $$A1$$) and (b = $$B1$$))))))",
				inst.formulate(bounds.clone(), x, formula, -1, 2, false).toString());

		assertEquals("after(((a = ($$A0$$ + $$A2$$)) and (b = $$B2$$)))",
				inst.formulate(bounds.clone(), x, formula, 1, 1, false).toString());

		assertEquals(
				"after((((a = ($$A0$$ + $$A2$$)) and (b = $$B2$$)) and after((((a = $$A1$$) and (b = $$B1$$)) and after((((a = ($$A0$$ + $$A2$$)) and (b = $$B2$$)) and after((((a = $$A1$$) and (b = $$B1$$)) and after(((a = ($$A0$$ + $$A2$$)) and (b = $$B2$$)))))))))))",
				inst.formulate(bounds.clone(), x, formula, 1, 5, false).toString());

		inst0 = new Instance(uni);
		inst0.add(a, f.setOf("A0","A1","A2"));
		inst0.add(b, f.noneOf(1));
		inst1 = new Instance(uni);
		inst1.add(a, f.setOf("A1","A2"));
		inst1.add(b, f.setOf("B0","B1","B2"));
		inst2 = new Instance(uni);
		inst2.add(a, f.setOf("A0","A1","A2"));
		inst2.add(b, f.setOf("B0","B1","B2"));
		Instance inst3 = new Instance(uni);
		inst3.add(a, f.noneOf(1));
		inst3.add(b, f.setOf("B0","B1","B2"));
		inst = new TemporalInstance(Arrays.asList(inst0, inst1, inst2, inst3), 2, 1);
		
		opt.reporter().debug(inst.toString());

//		* state 0
//		relations: {a=[[A0], [A1], [A2]], b=[], $$A0$$=[[A0]], $$A1$$=[[A1]], $$A2$$=[[A2]], $$B0$$=[[B0]], $$B1$$=[[B1]], $$B2$$=[[B2]]}
//		* state 1
//		relations: {a=[[A1], [A2]], b=[[B0], [B1], [B2]], $$A0$$=[[A0]], $$A1$$=[[A1]], $$A2$$=[[A2]], $$B0$$=[[B0]], $$B1$$=[[B1]], $$B2$$=[[B2]]}
//		* state 2 LOOP
//		relations: {a=[[A0], [A1], [A2]], b=[[B0], [B1], [B2]], $$A0$$=[[A0]], $$A1$$=[[A1]], $$A2$$=[[A2]], $$B0$$=[[B0]], $$B1$$=[[B1]], $$B2$$=[[B2]]}
//		* state 3 LAST
//		relations: {a=[], b=[[B0], [B1], [B2]], $$A0$$=[[A0]], $$A1$$=[[A1]], $$A2$$=[[A2]], $$B0$$=[[B0]], $$B1$$=[[B1]], $$B2$$=[[B2]]}

		assertEquals(
				"after((((a = ($$A1$$ + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) and after(((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))))))",
				inst.formulate(bounds.clone(), x, formula, 1, 2, false).toString());

		assertEquals(
				"(after(after((((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) and after(((a = none) and (b = (($$B0$$ + $$B1$$) + $$B2$$))))))) and after(after(always(((((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) implies after(after(((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$)))))) and (((a = none) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) implies after(after(((a = none) and (b = (($$B0$$ + $$B1$$) + $$B2$$)))))))))))",
				inst.formulate(bounds.clone(), x, formula, 2, null, false).toString());

		assertEquals(
				"(((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = none)) and after((((a = ($$A1$$ + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) and after(((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$)))))))",
				inst.formulate(bounds.clone(), x, formula, 0, 2, false).toString());

		assertEquals(
				"(((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = none)) and after((((a = ($$A1$$ + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) and after(((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$)))))))",
				inst.formulate(bounds.clone(), x, formula, -1, 2, false).toString());

		assertEquals("after(((a = ($$A1$$ + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))))",
				inst.formulate(bounds.clone(), x, formula, 1, 1, false).toString());

		assertEquals(
				"after((((a = ($$A1$$ + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) and after((((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) and after((((a = none) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) and after((((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) and after(((a = none) and (b = (($$B0$$ + $$B1$$) + $$B2$$))))))))))))",
				inst.formulate(bounds.clone(), x, formula, 1, 5, false).toString());

	}

	/* Temporal segment reification with static configs. */
	@Test
	public void testTmpConfigSegmentReif() {
		int n = 2;

		Relation a = Relation.unary("a");
		Relation b = Relation.binary_variable("b");

		Object[] atoms = new Object[n * 2];
		for (int i = 0; i < n; i++)
			atoms[i] = "A" + i;
		for (int i = 0; i < n; i++)
			atoms[n + i] = "B" + i;

		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A" + (n - 1)));
		TupleSet bs = f.range(f.tuple("A0"), f.tuple("A" + (n - 1)))
				.product(f.range(f.tuple("B0"), f.tuple("B" + (n - 1))));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, as);
		bounds.bound(b, bs);
		Formula formula = ((b.eq(b.prime()).not())).always().and(a.no());

		ExtendedOptions opt = new ExtendedOptions();

//		opt.setReporter(new ConsoleReporter());

		Map<Object, Expression> x = new HashMap<Object, Expression>();

		Instance inst0 = new Instance(uni);
		inst0.add(a, f.noneOf(1));
		inst0.add(b, f.setOf(f.tuple("A0","B0"),f.tuple("A0","B1"),f.tuple("A1","B0")));
		Instance inst1 = new Instance(uni);
		inst1.add(a, f.noneOf(1));
		inst1.add(b, f.setOf(f.tuple("A0","B1"),f.tuple("A1","B0"),f.tuple("A1","B1")));
		TemporalInstance inst = new TemporalInstance(Arrays.asList(inst0, inst1), 0, 1);
		
		opt.reporter().debug(inst.toString());

//		* state 0 LOOP
//		relations: {a=[], b=[[A0, B0], [A0, B1], [A1, B0]]}
//		* state 1 LAST
//		relations: {a=[], b=[[A0, B1], [A1, B0], [A1, B1]]}

		assertEquals("(a = none)", inst.formulate(bounds.clone(), x, formula, -1, -1, false).toString());

		assertEquals(
				"after(((b = ((($$A0$$ -> $$B1$$) + ($$A1$$ -> $$B0$$)) + ($$A1$$ -> $$B1$$))) and after((b = ((($$A0$$ -> $$B0$$) + ($$A0$$ -> $$B1$$)) + ($$A1$$ -> $$B0$$))))))",
				inst.formulate(bounds.clone(), x, formula, 1, 2, false).toString());

		assertEquals(
				"(after(after(((b = ((($$A0$$ -> $$B0$$) + ($$A0$$ -> $$B1$$)) + ($$A1$$ -> $$B0$$))) and after((b = ((($$A0$$ -> $$B1$$) + ($$A1$$ -> $$B0$$)) + ($$A1$$ -> $$B1$$))))))) and always((((b = ((($$A0$$ -> $$B0$$) + ($$A0$$ -> $$B1$$)) + ($$A1$$ -> $$B0$$))) implies after(after((b = ((($$A0$$ -> $$B0$$) + ($$A0$$ -> $$B1$$)) + ($$A1$$ -> $$B0$$)))))) and ((b = ((($$A0$$ -> $$B1$$) + ($$A1$$ -> $$B0$$)) + ($$A1$$ -> $$B1$$))) implies after(after((b = ((($$A0$$ -> $$B1$$) + ($$A1$$ -> $$B0$$)) + ($$A1$$ -> $$B1$$)))))))))",
				inst.formulate(bounds.clone(), x, formula, 2, null, false).toString());

		assertEquals(
				"((b = ((($$A0$$ -> $$B0$$) + ($$A0$$ -> $$B1$$)) + ($$A1$$ -> $$B0$$))) and after(((b = ((($$A0$$ -> $$B1$$) + ($$A1$$ -> $$B0$$)) + ($$A1$$ -> $$B1$$))) and after((b = ((($$A0$$ -> $$B0$$) + ($$A0$$ -> $$B1$$)) + ($$A1$$ -> $$B0$$)))))))",
				inst.formulate(bounds.clone(), x, formula, 0, 2, false).toString());

		assertEquals(
				"((a = none) and ((b = ((($$A0$$ -> $$B0$$) + ($$A0$$ -> $$B1$$)) + ($$A1$$ -> $$B0$$))) and after(((b = ((($$A0$$ -> $$B1$$) + ($$A1$$ -> $$B0$$)) + ($$A1$$ -> $$B1$$))) and after((b = ((($$A0$$ -> $$B0$$) + ($$A0$$ -> $$B1$$)) + ($$A1$$ -> $$B0$$))))))))",
				inst.formulate(bounds.clone(), x, formula, -1, 2, false).toString());

		assertEquals("after((b = ((($$A0$$ -> $$B1$$) + ($$A1$$ -> $$B0$$)) + ($$A1$$ -> $$B1$$))))", inst.formulate(bounds.clone(), x, formula, 1, 1, false).toString());

		assertEquals(
				"after(((b = ((($$A0$$ -> $$B1$$) + ($$A1$$ -> $$B0$$)) + ($$A1$$ -> $$B1$$))) and after(((b = ((($$A0$$ -> $$B0$$) + ($$A0$$ -> $$B1$$)) + ($$A1$$ -> $$B0$$))) and after(((b = ((($$A0$$ -> $$B1$$) + ($$A1$$ -> $$B0$$)) + ($$A1$$ -> $$B1$$))) and after(((b = ((($$A0$$ -> $$B0$$) + ($$A0$$ -> $$B1$$)) + ($$A1$$ -> $$B0$$))) and after((b = ((($$A0$$ -> $$B1$$) + ($$A1$$ -> $$B0$$)) + ($$A1$$ -> $$B1$$))))))))))))",
				inst.formulate(bounds.clone(), x, formula, 1, 5, false).toString());

		inst0 = new Instance(uni);
		inst0.add(a, f.noneOf(1));
		inst0.add(b, f.setOf(f.tuple("A0","B1"),f.tuple("A1","B0")));
		inst1 = new Instance(uni);
		inst1.add(a, f.noneOf(1));
		inst1.add(b, f.setOf(f.tuple("A0","B0"),f.tuple("A1","B1")));
		inst = new TemporalInstance(Arrays.asList(inst0, inst1), 0, 1);
		
		opt.reporter().debug(inst.toString());

//		* state 0 LOOP
//		relations: {a=[], b=[[A0, B1], [A1, B0]]}
//		* state 1 LAST
//		relations: {a=[], b=[[A0, B0], [A1, B1]]}

		assertEquals("after(((b = (($$A0$$ -> $$B0$$) + ($$A1$$ -> $$B1$$))) and after((b = (($$A0$$ -> $$B1$$) + ($$A1$$ -> $$B0$$))))))",
				inst.formulate(bounds.clone(), x, formula, 1, 2, false).toString());

		assertEquals(
				"(after(after(((b = (($$A0$$ -> $$B1$$) + ($$A1$$ -> $$B0$$))) and after((b = (($$A0$$ -> $$B0$$) + ($$A1$$ -> $$B1$$))))))) and always((((b = (($$A0$$ -> $$B1$$) + ($$A1$$ -> $$B0$$))) implies after(after((b = (($$A0$$ -> $$B1$$) + ($$A1$$ -> $$B0$$)))))) and ((b = (($$A0$$ -> $$B0$$) + ($$A1$$ -> $$B1$$))) implies after(after((b = (($$A0$$ -> $$B0$$) + ($$A1$$ -> $$B1$$)))))))))",
				inst.formulate(bounds.clone(), x, formula, 2, null, false).toString());

		assertEquals(
				"((b = (($$A0$$ -> $$B1$$) + ($$A1$$ -> $$B0$$))) and after(((b = (($$A0$$ -> $$B0$$) + ($$A1$$ -> $$B1$$))) and after((b = (($$A0$$ -> $$B1$$) + ($$A1$$ -> $$B0$$)))))))",
				inst.formulate(bounds.clone(), x, formula, 0, 2, false).toString());

		assertEquals(
				"((a = none) and ((b = (($$A0$$ -> $$B1$$) + ($$A1$$ -> $$B0$$))) and after(((b = (($$A0$$ -> $$B0$$) + ($$A1$$ -> $$B1$$))) and after((b = (($$A0$$ -> $$B1$$) + ($$A1$$ -> $$B0$$))))))))",
				inst.formulate(bounds.clone(), x, formula, -1, 2, false).toString());

		assertEquals("after((b = (($$A0$$ -> $$B0$$) + ($$A1$$ -> $$B1$$))))", inst.formulate(bounds.clone(), x, formula, 1, 1, false).toString());

		assertEquals(
				"after(((b = (($$A0$$ -> $$B0$$) + ($$A1$$ -> $$B1$$))) and after(((b = (($$A0$$ -> $$B1$$) + ($$A1$$ -> $$B0$$))) and after(((b = (($$A0$$ -> $$B0$$) + ($$A1$$ -> $$B1$$))) and after(((b = (($$A0$$ -> $$B1$$) + ($$A1$$ -> $$B0$$))) and after((b = (($$A0$$ -> $$B0$$) + ($$A1$$ -> $$B1$$))))))))))))",
				inst.formulate(bounds.clone(), x, formula, 1, 5, false).toString());

	}

	/* Static reification. */
	@Test
	public void testStaticSome() {
		int n = 3;

		Relation a = Relation.unary("a");
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
		Formula formula = a.some().and(b.some());

		ExtendedOptions opt = new ExtendedOptions();

		Map<Object, Expression> x = new HashMap<Object, Expression>();

		Instance inst = new Instance(uni);
		inst.add(a, f.setOf("A"+(n-1)));
		inst.add(b, f.setOf("B"+(n-1)));

		opt.reporter().debug(inst.toString());
//		opt.reporter().debug(inst.formulate(bounds,x,formula));
//		opt.reporter().debug(x);

//		relations: {a=[[A2]], b=[[B2]]}

		assertEquals("((a = A2) and (b = B2))", inst.formulate(x, formula, true, bounds.clone()).toString());

		formula = formula.and(inst.formulate(x, formula, true, bounds).not());

		inst = new Instance(uni);
		inst.add(a, f.setOf("A1","A2"));
		inst.add(b, f.setOf("B1","B2"));

		opt.reporter().debug(inst.toString());
//		opt.reporter().debug(inst.formulate(bounds,x,formula));
//		opt.reporter().debug(x);

//		relations: {a=[[A1], [A2]], b=[[B1], [B2]], $$A2$$=[[A2]], $$B2$$=[[B2]], $$A0$$=[[A0]], $$A1$$=[[A1]], $$B0$$=[[B0]], $$B1$$=[[B1]]}

		assertEquals("((a = (A1 + A2)) and (b = (B1 + B2)))",
				inst.formulate(x, formula, true, bounds.clone()).toString());

		formula = formula.and(inst.formulate(x, formula, true, bounds).not());

		inst = new Instance(uni);
		inst.add(a, f.setOf("A1","A2"));
		inst.add(b, f.setOf("B2"));

		opt.reporter().debug(inst.toString());
//		opt.reporter().debug(inst.formulate(bounds,x,formula));
//		opt.reporter().debug(x);

//		relations: {a=[[A1], [A2]], b=[[B2]], $$A1$$=[[A1]], $$A2$$=[[A2]], $$B1$$=[[B1]], $$B2$$=[[B2]], $$A0$$=[[A0]], $$B0$$=[[B0]]}

		assertEquals("((a = (A1 + A2)) and (b = B2))",
				inst.formulate(x, formula, true, bounds.clone()).toString());

	}

	/* Temporal reification, not all relations relevant, loop not first. */
	@Test
	public void testTmpSome() {
		int n = 3;

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
		Formula formula = ((a.eq(a.prime()).not())).always();

		ExtendedOptions opt = new ExtendedOptions();

//		opt.setReporter(new SLF4JReporter());
		opt.setRunTemporal(true);
		opt.setRunUnbounded(false);
		opt.setRunDecomposed(false);

		Map<Object, Expression> x = new HashMap<Object, Expression>();

		Instance inst0 = new Instance(uni);
		inst0.add(a, f.noneOf(1));
		inst0.add(b, f.noneOf(1));
		Instance inst1 = new Instance(uni);
		inst1.add(a, f.setOf("A0","A1","A2"));
		inst1.add(b, f.noneOf(1));
		TemporalInstance inst = new TemporalInstance(Arrays.asList(inst0, inst1), 0, 1);

		opt.reporter().debug(inst.toString());

//		* state 0 LOOP
//		relations: {a=[], b=[]}
//		* state 1 LAST
//		relations: {a=[[A0], [A1], [A2]], b=[]}

		assertEquals(
				"(some [A1: one univ, B2: one univ, A2: one univ, B0: one univ, A0: one univ, B1: one univ] | (((((((A1 + B2) + A2) + B0) + A0) + B1) = univ) and (((a = none) and after((a = ((A0 + A1) + A2)))) and always((((a = none) implies after(after((a = none)))) and ((a = ((A0 + A1) + A2)) implies after(after((a = ((A0 + A1) + A2))))))))))",
				inst.formulate(x, formula, true, bounds.clone()).toString());

		inst0 = new Instance(uni);
		inst0.add(a, f.setOf("A2"));
		inst0.add(b, f.noneOf(1));
		inst1 = new Instance(uni);
		inst1.add(a, f.setOf("A0","A1"));
		inst1.add(b, f.noneOf(1));
		inst = new TemporalInstance(Arrays.asList(inst0, inst1), 0, 1);
		
		opt.reporter().debug(inst.toString());

//		* state 0 LOOP
//		relations: {a=[[A2]], b=[]}
//		* state 1 LAST
//		relations: {a=[[A0], [A1]], b=[]}
		
		assertEquals(
				"(some [A1: one univ, B2: one univ, A2: one univ, B0: one univ, A0: one univ, B1: one univ] | (((((((A1 + B2) + A2) + B0) + A0) + B1) = univ) and (((a = A2) and after((a = (A0 + A1)))) and always((((a = A2) implies after(after((a = A2)))) and ((a = (A0 + A1)) implies after(after((a = (A0 + A1))))))))))",
				inst.formulate(x, formula, true, bounds.clone()).toString());

	}

	/* Temporal reification. */
	@Test
	public void testTmp2Some() {
		int n = 3;

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
		Formula formula = ((a.eq(a.prime()).not())).always().and(b.no().and(b.some().always().after()));

		ExtendedOptions opt = new ExtendedOptions();

//		opt.setReporter(new SLF4JReporter());

		Map<Object, Expression> x = new HashMap<Object, Expression>();

		Instance inst0 = new Instance(uni);
		inst0.add(a, f.setOf("A1","A2"));
		inst0.add(b, f.noneOf(1));
		Instance inst1 = new Instance(uni);
		inst1.add(a, f.noneOf(1));
		inst1.add(b, f.setOf("B2"));
		Instance inst2 = new Instance(uni);
		inst2.add(a, f.setOf("A0"));
		inst2.add(b, f.setOf("B2"));
		TemporalInstance inst = new TemporalInstance(Arrays.asList(inst0, inst1, inst2), 1, 1);
		
		opt.reporter().debug(inst.toString());

//		* state 0
//		relations: {a=[[A1], [A2]], b=[]}
//		* state 1 LOOP
//		relations: {a=[], b=[[B2]]}
//		* state 2 LAST
//		relations: {a=[[A0]], b=[[B2]]}

		assertEquals(
				"(some [A1: one univ, B2: one univ, A2: one univ, B0: one univ, A0: one univ, B1: one univ] | (((((((A1 + B2) + A2) + B0) + A0) + B1) = univ) and ((((a = (A1 + A2)) and (b = none)) and after((((a = none) and (b = B2)) and after(((a = A0) and (b = B2)))))) and after(always(((((a = none) and (b = B2)) implies after(after(((a = none) and (b = B2))))) and (((a = A0) and (b = B2)) implies after(after(((a = A0) and (b = B2)))))))))))",
				inst.formulate(x, formula, true, bounds.clone()).toString());

		inst0 = new Instance(uni);
		inst0.add(a, f.setOf("A1","A2"));
		inst0.add(b, f.noneOf(1));
		inst1 = new Instance(uni);
		inst1.add(a, f.noneOf(1));
		inst1.add(b, f.setOf("B2"));
		inst2 = new Instance(uni);
		inst2.add(a, f.setOf("A0"));
		inst2.add(b, f.setOf("B2"));
		inst = new TemporalInstance(Arrays.asList(inst0, inst1, inst2), 1, 1);
		
		opt.reporter().debug(inst.toString());

//		* state 0
//		relations: {a=[[A1], [A2]], b=[], $$A0$$=[[A0]], $$A1$$=[[A1]], $$A2$$=[[A2]], $$B0$$=[[B0]], $$B1$$=[[B1]], $$B2$$=[[B2]]}
//		* state 1 LOOP
//		relations: {a=[], b=[[B2]], $$A0$$=[[A0]], $$A1$$=[[A1]], $$A2$$=[[A2]], $$B0$$=[[B0]], $$B1$$=[[B1]], $$B2$$=[[B2]]}
//		* state 2 LAST
//		relations: {a=[[A0]], b=[[B2]], $$A0$$=[[A0]], $$A1$$=[[A1]], $$A2$$=[[A2]], $$B0$$=[[B0]], $$B1$$=[[B1]], $$B2$$=[[B2]]}

		assertEquals(
				"(some [A1: one univ, B2: one univ, A2: one univ, B0: one univ, A0: one univ, B1: one univ] | (((((((A1 + B2) + A2) + B0) + A0) + B1) = univ) and ((((a = (A1 + A2)) and (b = none)) and after((((a = none) and (b = B2)) and after(((a = A0) and (b = B2)))))) and after(always(((((a = none) and (b = B2)) implies after(after(((a = none) and (b = B2))))) and (((a = A0) and (b = B2)) implies after(after(((a = A0) and (b = B2)))))))))))",
				inst.formulate(x, formula, true, bounds.clone()).toString());

	}

	/* Temporal segment reification. */
	@Test
	public void testTmpSegmentSome() {
		int n = 3;

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
		Formula formula = ((a.eq(a.prime()).not())).always().and(b.no().and(b.some().always().after()));

		ExtendedOptions opt = new ExtendedOptions();

//		opt.setReporter(new ConsoleReporter());

		Map<Object, Expression> x = new HashMap<Object, Expression>();

		Instance inst0 = new Instance(uni);
		inst0.add(a, f.setOf("A0","A1","A2"));
		inst0.add(b, f.noneOf(1));
		Instance inst1 = new Instance(uni);
		inst1.add(a, f.setOf("A1","A2"));
		inst1.add(b, f.setOf("B0","B1","B2"));
		Instance inst2 = new Instance(uni);
		inst2.add(a, f.setOf("A0","A1","A2"));
		inst2.add(b, f.setOf("B0","B1","B2"));
		TemporalInstance inst = new TemporalInstance(Arrays.asList(inst0, inst1, inst2), 1, 1);
		
		opt.reporter().debug(inst.toString());

//		* state 0
//		relations: {a=[[A0], [A1], [A2]], b=[]}
//		* state 1 LOOP
//		relations: {a=[[A1], [A2]], b=[[B0], [B1], [B2]]}
//		* state 2 LAST
//		relations: {a=[[A0], [A1], [A2]], b=[[B0], [B1], [B2]]}

		assertEquals("(some [A1: one univ, B2: one univ, A2: one univ, B0: one univ, A0: one univ, B1: one univ] | (((((((A1 + B2) + A2) + B0) + A0) + B1) = univ) and true))", inst.formulate(bounds.clone(), x, formula, -1, -1, true).toString());

		assertEquals(
				"(some [A1: one univ, B2: one univ, A2: one univ, B0: one univ, A0: one univ, B1: one univ] | (((((((A1 + B2) + A2) + B0) + A0) + B1) = univ) and after((((a = (A1 + A2)) and (b = ((B0 + B1) + B2))) and after(((a = ((A0 + A1) + A2)) and (b = ((B0 + B1) + B2))))))))",
				inst.formulate(bounds.clone(), x, formula, 1, 2, true).toString());

		assertEquals(
				"(some [A1: one univ, B2: one univ, A2: one univ, B0: one univ, A0: one univ, B1: one univ] | (((((((A1 + B2) + A2) + B0) + A0) + B1) = univ) and (after(after((((a = ((A0 + A1) + A2)) and (b = ((B0 + B1) + B2))) and after(((a = (A1 + A2)) and (b = ((B0 + B1) + B2))))))) and after(always(((((a = (A1 + A2)) and (b = ((B0 + B1) + B2))) implies after(after(((a = (A1 + A2)) and (b = ((B0 + B1) + B2)))))) and (((a = ((A0 + A1) + A2)) and (b = ((B0 + B1) + B2))) implies after(after(((a = ((A0 + A1) + A2)) and (b = ((B0 + B1) + B2))))))))))))",
				inst.formulate(bounds.clone(), x, formula, 2, null, true).toString());

		assertEquals(
				"(some [A1: one univ, B2: one univ, A2: one univ, B0: one univ, A0: one univ, B1: one univ] | (((((((A1 + B2) + A2) + B0) + A0) + B1) = univ) and (((a = ((A0 + A1) + A2)) and (b = none)) and after((((a = (A1 + A2)) and (b = ((B0 + B1) + B2))) and after(((a = ((A0 + A1) + A2)) and (b = ((B0 + B1) + B2)))))))))",
				inst.formulate(bounds.clone(), x, formula, 0, 2, true).toString());

		assertEquals(
				"(some [A1: one univ, B2: one univ, A2: one univ, B0: one univ, A0: one univ, B1: one univ] | (((((((A1 + B2) + A2) + B0) + A0) + B1) = univ) and (((a = ((A0 + A1) + A2)) and (b = none)) and after((((a = (A1 + A2)) and (b = ((B0 + B1) + B2))) and after(((a = ((A0 + A1) + A2)) and (b = ((B0 + B1) + B2)))))))))",
				inst.formulate(bounds.clone(), x, formula, -1, 2, true).toString());

		assertEquals("(some [A1: one univ, B2: one univ, A2: one univ, B0: one univ, A0: one univ, B1: one univ] | (((((((A1 + B2) + A2) + B0) + A0) + B1) = univ) and after(((a = (A1 + A2)) and (b = ((B0 + B1) + B2))))))",
				inst.formulate(bounds.clone(), x, formula, 1, 1, true).toString());

		assertEquals(
				"(some [A1: one univ, B2: one univ, A2: one univ, B0: one univ, A0: one univ, B1: one univ] | (((((((A1 + B2) + A2) + B0) + A0) + B1) = univ) and after((((a = (A1 + A2)) and (b = ((B0 + B1) + B2))) and after((((a = ((A0 + A1) + A2)) and (b = ((B0 + B1) + B2))) and after((((a = (A1 + A2)) and (b = ((B0 + B1) + B2))) and after((((a = ((A0 + A1) + A2)) and (b = ((B0 + B1) + B2))) and after(((a = (A1 + A2)) and (b = ((B0 + B1) + B2))))))))))))))",
				inst.formulate(bounds.clone(), x, formula, 1, 5, true).toString());

		inst0 = new Instance(uni);
		inst0.add(a, f.setOf("A0","A1","A2"));
		inst0.add(b, f.noneOf(1));
		inst1 = new Instance(uni);
		inst1.add(a, f.setOf("A1","A2"));
		inst1.add(b, f.setOf("B0","B1","B2"));
		inst2 = new Instance(uni);
		inst2.add(a, f.setOf("A0","A1","A2"));
		inst2.add(b, f.setOf("B0","B1","B2"));
		Instance inst3 = new Instance(uni);
		inst3.add(a, f.noneOf(1));
		inst3.add(b, f.setOf("B0","B1","B2"));
		inst = new TemporalInstance(Arrays.asList(inst0, inst1, inst2, inst3), 2, 1);
		
		opt.reporter().debug(inst.toString());

//		* state 0
//		relations: {a=[[A0], [A1], [A2]], b=[], $$A0$$=[[A0]], $$A1$$=[[A1]], $$A2$$=[[A2]], $$B0$$=[[B0]], $$B1$$=[[B1]], $$B2$$=[[B2]]}
//		* state 1
//		relations: {a=[[A1], [A2]], b=[[B0], [B1], [B2]], $$A0$$=[[A0]], $$A1$$=[[A1]], $$A2$$=[[A2]], $$B0$$=[[B0]], $$B1$$=[[B1]], $$B2$$=[[B2]]}
//		* state 2 LOOP
//		relations: {a=[[A0], [A1], [A2]], b=[[B0], [B1], [B2]], $$A0$$=[[A0]], $$A1$$=[[A1]], $$A2$$=[[A2]], $$B0$$=[[B0]], $$B1$$=[[B1]], $$B2$$=[[B2]]}
//		* state 3 LAST
//		relations: {a=[], b=[[B0], [B1], [B2]], $$A0$$=[[A0]], $$A1$$=[[A1]], $$A2$$=[[A2]], $$B0$$=[[B0]], $$B1$$=[[B1]], $$B2$$=[[B2]]}

		assertEquals(
				"(some [A1: one univ, B2: one univ, A2: one univ, B0: one univ, A0: one univ, B1: one univ] | (((((((A1 + B2) + A2) + B0) + A0) + B1) = univ) and after((((a = (A1 + A2)) and (b = ((B0 + B1) + B2))) and after(((a = ((A0 + A1) + A2)) and (b = ((B0 + B1) + B2))))))))",
				inst.formulate(bounds.clone(), x, formula, 1, 2, true).toString());

		assertEquals(
				"(some [A1: one univ, B2: one univ, A2: one univ, B0: one univ, A0: one univ, B1: one univ] | (((((((A1 + B2) + A2) + B0) + A0) + B1) = univ) and (after(after((((a = ((A0 + A1) + A2)) and (b = ((B0 + B1) + B2))) and after(((a = none) and (b = ((B0 + B1) + B2))))))) and after(after(always(((((a = ((A0 + A1) + A2)) and (b = ((B0 + B1) + B2))) implies after(after(((a = ((A0 + A1) + A2)) and (b = ((B0 + B1) + B2)))))) and (((a = none) and (b = ((B0 + B1) + B2))) implies after(after(((a = none) and (b = ((B0 + B1) + B2)))))))))))))",
				inst.formulate(bounds.clone(), x, formula, 2, null, true).toString());

		assertEquals(
				"(some [A1: one univ, B2: one univ, A2: one univ, B0: one univ, A0: one univ, B1: one univ] | (((((((A1 + B2) + A2) + B0) + A0) + B1) = univ) and (((a = ((A0 + A1) + A2)) and (b = none)) and after((((a = (A1 + A2)) and (b = ((B0 + B1) + B2))) and after(((a = ((A0 + A1) + A2)) and (b = ((B0 + B1) + B2)))))))))",
				inst.formulate(bounds.clone(), x, formula, 0, 2, true).toString());

		assertEquals(
				"(some [A1: one univ, B2: one univ, A2: one univ, B0: one univ, A0: one univ, B1: one univ] | (((((((A1 + B2) + A2) + B0) + A0) + B1) = univ) and (((a = ((A0 + A1) + A2)) and (b = none)) and after((((a = (A1 + A2)) and (b = ((B0 + B1) + B2))) and after(((a = ((A0 + A1) + A2)) and (b = ((B0 + B1) + B2)))))))))",
				inst.formulate(bounds.clone(), x, formula, -1, 2, true).toString());

		assertEquals("(some [A1: one univ, B2: one univ, A2: one univ, B0: one univ, A0: one univ, B1: one univ] | (((((((A1 + B2) + A2) + B0) + A0) + B1) = univ) and after(((a = (A1 + A2)) and (b = ((B0 + B1) + B2))))))",
				inst.formulate(bounds.clone(), x, formula, 1, 1, true).toString());

		assertEquals(
				"(some [A1: one univ, B2: one univ, A2: one univ, B0: one univ, A0: one univ, B1: one univ] | (((((((A1 + B2) + A2) + B0) + A0) + B1) = univ) and after((((a = (A1 + A2)) and (b = ((B0 + B1) + B2))) and after((((a = ((A0 + A1) + A2)) and (b = ((B0 + B1) + B2))) and after((((a = none) and (b = ((B0 + B1) + B2))) and after((((a = ((A0 + A1) + A2)) and (b = ((B0 + B1) + B2))) and after(((a = none) and (b = ((B0 + B1) + B2))))))))))))))",
				inst.formulate(bounds.clone(), x, formula, 1, 5, true).toString());

	}

	/* Temporal segment reification with static configs. */
	@Test
	public void testTmpConfigSegmentSome() {
		int n = 2;

		Relation a = Relation.unary("a");
		Relation b = Relation.binary_variable("b");

		Object[] atoms = new Object[n * 2];
		for (int i = 0; i < n; i++)
			atoms[i] = "A" + i;
		for (int i = 0; i < n; i++)
			atoms[n + i] = "B" + i;

		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A" + (n - 1)));
		TupleSet bs = f.range(f.tuple("A0"), f.tuple("A" + (n - 1)))
				.product(f.range(f.tuple("B0"), f.tuple("B" + (n - 1))));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, as);
		bounds.bound(b, bs);
		Formula formula = ((b.eq(b.prime()).not())).always().and(a.no());

		ExtendedOptions opt = new ExtendedOptions();

//		opt.setReporter(new ConsoleReporter());

		Map<Object, Expression> x = new HashMap<Object, Expression>();
		
		Instance inst0 = new Instance(uni);
		inst0.add(a, f.noneOf(1));
		inst0.add(b, f.setOf(f.tuple("A0","B0"),f.tuple("A0","B1"),f.tuple("A1","B0")));
		Instance inst1 = new Instance(uni);
		inst1.add(a, f.noneOf(1));
		inst1.add(b, f.setOf(f.tuple("A0","B1"),f.tuple("A1","B0"),f.tuple("A1","B1")));
		TemporalInstance inst = new TemporalInstance(Arrays.asList(inst0, inst1), 0, 1);
		
		opt.reporter().debug(inst.toString());

//		* state 0 LOOP
//		relations: {a=[], b=[[A0, B0], [A0, B1], [A1, B0]]}
//		* state 1 LAST
//		relations: {a=[], b=[[A0, B1], [A1, B0], [A1, B1]]}

		assertEquals("(some [A1: one univ, B0: one univ, A0: one univ, B1: one univ] | (((((A1 + B0) + A0) + B1) = univ) and (a = none)))", inst.formulate(bounds.clone(), x, formula, -1, -1, true).toString());

		assertEquals(
				"(some [A1: one univ, B0: one univ, A0: one univ, B1: one univ] | (((((A1 + B0) + A0) + B1) = univ) and after(((b = (((A0 -> B1) + (A1 -> B0)) + (A1 -> B1))) and after((b = (((A0 -> B0) + (A0 -> B1)) + (A1 -> B0))))))))",
				inst.formulate(bounds.clone(), x, formula, 1, 2, true).toString());

		assertEquals(
				"(some [A1: one univ, B0: one univ, A0: one univ, B1: one univ] | (((((A1 + B0) + A0) + B1) = univ) and (after(after(((b = (((A0 -> B0) + (A0 -> B1)) + (A1 -> B0))) and after((b = (((A0 -> B1) + (A1 -> B0)) + (A1 -> B1))))))) and always((((b = (((A0 -> B0) + (A0 -> B1)) + (A1 -> B0))) implies after(after((b = (((A0 -> B0) + (A0 -> B1)) + (A1 -> B0)))))) and ((b = (((A0 -> B1) + (A1 -> B0)) + (A1 -> B1))) implies after(after((b = (((A0 -> B1) + (A1 -> B0)) + (A1 -> B1)))))))))))",
				inst.formulate(bounds.clone(), x, formula, 2, null, true).toString());

		assertEquals(
				"(some [A1: one univ, B0: one univ, A0: one univ, B1: one univ] | (((((A1 + B0) + A0) + B1) = univ) and ((b = (((A0 -> B0) + (A0 -> B1)) + (A1 -> B0))) and after(((b = (((A0 -> B1) + (A1 -> B0)) + (A1 -> B1))) and after((b = (((A0 -> B0) + (A0 -> B1)) + (A1 -> B0)))))))))",
				inst.formulate(bounds.clone(), x, formula, 0, 2, true).toString());

		assertEquals(
				"(some [A1: one univ, B0: one univ, A0: one univ, B1: one univ] | (((((A1 + B0) + A0) + B1) = univ) and ((a = none) and ((b = (((A0 -> B0) + (A0 -> B1)) + (A1 -> B0))) and after(((b = (((A0 -> B1) + (A1 -> B0)) + (A1 -> B1))) and after((b = (((A0 -> B0) + (A0 -> B1)) + (A1 -> B0))))))))))",
				inst.formulate(bounds.clone(), x, formula, -1, 2, true).toString());

		assertEquals("(some [A1: one univ, B0: one univ, A0: one univ, B1: one univ] | (((((A1 + B0) + A0) + B1) = univ) and after((b = (((A0 -> B1) + (A1 -> B0)) + (A1 -> B1))))))", inst.formulate(bounds.clone(), x, formula, 1, 1, true).toString());

		assertEquals(
				"(some [A1: one univ, B0: one univ, A0: one univ, B1: one univ] | (((((A1 + B0) + A0) + B1) = univ) and after(((b = (((A0 -> B1) + (A1 -> B0)) + (A1 -> B1))) and after(((b = (((A0 -> B0) + (A0 -> B1)) + (A1 -> B0))) and after(((b = (((A0 -> B1) + (A1 -> B0)) + (A1 -> B1))) and after(((b = (((A0 -> B0) + (A0 -> B1)) + (A1 -> B0))) and after((b = (((A0 -> B1) + (A1 -> B0)) + (A1 -> B1))))))))))))))",
				inst.formulate(bounds.clone(), x, formula, 1, 5, true).toString());

		inst0 = new Instance(uni);
		inst0.add(a, f.noneOf(1));
		inst0.add(b, f.setOf(f.tuple("A0","B1"),f.tuple("A1","B0")));
		inst1 = new Instance(uni);
		inst1.add(a, f.noneOf(1));
		inst1.add(b, f.setOf(f.tuple("A0","B0"),f.tuple("A1","B1")));
		inst = new TemporalInstance(Arrays.asList(inst0, inst1), 0, 1);

		opt.reporter().debug(inst.toString());

//		* state 0 LOOP
//		relations: {a=[], b=[[A0, B1], [A1, B0]]}
//		* state 1 LAST
//		relations: {a=[], b=[[A0, B0], [A1, B1]]}

		assertEquals("(some [A1: one univ, B0: one univ, A0: one univ, B1: one univ] | (((((A1 + B0) + A0) + B1) = univ) and after(((b = ((A0 -> B0) + (A1 -> B1))) and after((b = ((A0 -> B1) + (A1 -> B0))))))))",
				inst.formulate(bounds.clone(), x, formula, 1, 2, true).toString());

		assertEquals(
				"(some [A1: one univ, B0: one univ, A0: one univ, B1: one univ] | (((((A1 + B0) + A0) + B1) = univ) and (after(after(((b = ((A0 -> B1) + (A1 -> B0))) and after((b = ((A0 -> B0) + (A1 -> B1))))))) and always((((b = ((A0 -> B1) + (A1 -> B0))) implies after(after((b = ((A0 -> B1) + (A1 -> B0)))))) and ((b = ((A0 -> B0) + (A1 -> B1))) implies after(after((b = ((A0 -> B0) + (A1 -> B1)))))))))))",
				inst.formulate(bounds.clone(), x, formula, 2, null, true).toString());

		assertEquals(
				"(some [A1: one univ, B0: one univ, A0: one univ, B1: one univ] | (((((A1 + B0) + A0) + B1) = univ) and ((b = ((A0 -> B1) + (A1 -> B0))) and after(((b = ((A0 -> B0) + (A1 -> B1))) and after((b = ((A0 -> B1) + (A1 -> B0)))))))))",
				inst.formulate(bounds.clone(), x, formula, 0, 2, true).toString());

		assertEquals(
				"(some [A1: one univ, B0: one univ, A0: one univ, B1: one univ] | (((((A1 + B0) + A0) + B1) = univ) and ((a = none) and ((b = ((A0 -> B1) + (A1 -> B0))) and after(((b = ((A0 -> B0) + (A1 -> B1))) and after((b = ((A0 -> B1) + (A1 -> B0))))))))))",
				inst.formulate(bounds.clone(), x, formula, -1, 2, true).toString());

		assertEquals("(some [A1: one univ, B0: one univ, A0: one univ, B1: one univ] | (((((A1 + B0) + A0) + B1) = univ) and after((b = ((A0 -> B0) + (A1 -> B1))))))", inst.formulate(bounds.clone(), x, formula, 1, 1, true).toString());

		assertEquals(
				"(some [A1: one univ, B0: one univ, A0: one univ, B1: one univ] | (((((A1 + B0) + A0) + B1) = univ) and after(((b = ((A0 -> B0) + (A1 -> B1))) and after(((b = ((A0 -> B1) + (A1 -> B0))) and after(((b = ((A0 -> B0) + (A1 -> B1))) and after(((b = ((A0 -> B1) + (A1 -> B0))) and after((b = ((A0 -> B0) + (A1 -> B1))))))))))))))",
				inst.formulate(bounds.clone(), x, formula, 1, 5, true).toString());

	}
}
