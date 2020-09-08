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
package kodkod.examples.pardinus.target;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.Explorer;
import kodkod.engine.PardinusSolver;
import kodkod.engine.Solution;
import kodkod.engine.config.ConsoleReporter;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.config.TargetOptions.TMode;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

/**
 * Basic target-oriented runnign example.
 * 
 * @author Nuno Macedo // [HASLab] target-oriented model finding
 */
public class BaseRun {
	private static PardinusSolver dsolver;
	private static ExtendedOptions opt;

	public static void main(String[] args) throws InterruptedException {
		opt = new ExtendedOptions();
		// needs a PMaxSAT solver 
		opt.setSolver(SATFactory.PMaxSAT4J);
		opt.setRunTarget(true);
		opt.setReporter(new ConsoleReporter());
		dsolver = new PardinusSolver(opt);

		int n = 4;

		Relation a = Relation.unary("a"), b = Relation.unary("b");

		Object[] atoms = new Object[n];
		for (int i = 0; i < n; i++)
			atoms[i] = "A" + i;

		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet ub = f.range(f.tuple("A0"), f.tuple("A" + (n - 1)));
		TupleSet lb = f.range(f.tuple("A0"), f.tuple("A0"));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, lb, ub);
		bounds.bound(b, ub);
		Formula formula = a.eq(Expression.UNIV).not().and(a.in(b));
		
		// set the initial target
		bounds.setTarget(a, bounds.lowerBound(a));
		bounds.setTarget(b, bounds.lowerBound(b));
		
		// solution closest or farthest from the target
		opt.setTargetMode(TMode.CLOSE);
		Explorer<Solution> sols = dsolver.solveAll(formula, bounds);
		
		// first solution will use set targets
		Solution sol = sols.next();
		System.out.println(sol.instance());

		// after first solution, targets are the previous solution
		for (int i = 0; i<4; i++) {
			sol = sols.next();
			opt.reporter().debug(sol.instance().toString());
		}

		// now will change as much as possible from previous
		opt.setTargetMode(TMode.FAR);
		for (int i = 0; i<4; i++) {
			sol = sols.next();
			opt.reporter().debug(sol.instance().toString());
		}
}
	
	
}
