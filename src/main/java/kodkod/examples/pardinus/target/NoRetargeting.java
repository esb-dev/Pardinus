package kodkod.examples.pardinus.target;

import kodkod.ast.*;
import kodkod.engine.*;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.fol2sat.Translation;
import kodkod.engine.satlab.SATFactory;
import kodkod.engine.satlab.TargetSATSolver;
import kodkod.instance.*;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

/**
 *   The {@link NoRetargeting} class demonstrates the Retargeter interface of Pardinus.
 *   Concretely, a Retargeter allows a caller to control target-oriented
 *   model-finding's retargeting pattern from the default (target
 *   the last found instance) to any pattern desired. Here, we show just
 *   the empty retargeter, which keeps the target constant, resulting
 *   in an enumeration of instances that are of monotonically non-decreasing
 *   distance from the target.

 *   The demo sets up a target-oriented model-finding problem
 *   with 2 atoms and 3 unary relations: p, q, and r.
 *
 *   Target for p: both atoms present.
 *   Target for q: no atoms present.
 *   Target for r: (no target).
 *
 *   Constraint: all 3 relations are non-empty.
 *
 * @author Tim Nelson
 */
public class NoRetargeting {

    public static void main(String[] args) {
        Relation p = Relation.unary("P");
        Relation q = Relation.unary("Q");
        Relation r = Relation.unary("R");

        // If an arg is passed, find *far* from target, rather than close.
        boolean findFar = (args.length > 0);
        System.out.println(Arrays.toString(args));

        Set<Object> atoms = new HashSet<>();
        int NATOMS = 2;
        for (int i = 0; i < NATOMS; i++) {
            atoms.add("Atom"+i);
        }
        Universe u = new Universe(atoms);

        PardinusBounds pb = new PardinusBounds(u);
        pb.bound(p, u.factory().allOf(1));
        pb.bound(q, u.factory().allOf(1));
        pb.bound(r, u.factory().allOf(1));

        // Target P = all, Q = none; R has no target
        // (but target won't satisfy fmla)
        pb.setTarget(p, u.factory().allOf(1));
        pb.setTarget(q, u.factory().noneOf(1));
        System.out.println("target for p: "+pb.target(p));
        System.out.println("target for q: "+pb.target(q));
        System.out.println("target for r: "+pb.target(r));

        Formula f = p.some().and(q.some()).and(r.some());
        System.out.println("formula = "+f);

        ///////////////////////////////////////////////////

        ExtendedOptions eo = new ExtendedOptions();
        eo.setRunTarget(true);
        eo.setSolver(SATFactory.PMaxSAT4J);
        eo.setSymmetryBreaking(20);
        eo.setLogTranslation(0);
        eo.setBitwidth(1); // minimal bitwidth allowed
        eo.setRetargeter(new Retargeter() {
            @Override
            public void retarget(Translation transl) {
                // Do nothing; keep initial target
            }
        });

        // We want to enumerate instances of maximal distance from
        // the target. But Pardinus will always produce a *first*
        // instance as close as possible to the initial target.
        // So instead, flip the bits of the target.

        // (Target-mode in options doesn't matter here)
        //eo.setTargetMode(TargetOptions.TMode.CLOSE);

        PardinusBounds origBounds = pb.clone(); // for displaying distance
        if(findFar) {
            // Flip initial target
            for(Relation rel : pb.targets().keySet()) {
                TupleSet tuples = u.factory().allOf(rel.arity());
                tuples.removeAll(pb.targets().get(rel));
                pb.setTarget(rel, tuples);
            }
            System.out.println("flipped target for p: " + pb.target(p));
            System.out.println("flipped target for q: " + pb.target(q));
            System.out.println("flipped target for r: " + pb.target(r));
        }

        PardinusSolver s = new PardinusSolver(eo);

        ///////////////////////////////////////////////////

        // Note: new "Explorer" iterator vs. Kodkod
        Explorer<Solution> sols =  s.solveAll(f, pb);
        int count = 0;
        while(sols.hasNext()) {
            Solution sol = sols.next();
            count++;
            if(sol.sat()) {
                System.out.println("-------------------");
                System.out.println(sol.instance().relationTuples());
                System.out.println("dist from target = "+computeDist(origBounds, sol.instance()));
            }
        }
        System.out.println("total number of instances: "+count);
    }

    /**
     * Compute Hamming distance between target and instance given
     * Relations not in target aren't counted.
     *
     * @param pb
     * @param instance
     * @return
     */
    private static int computeDist(PardinusBounds pb, Instance instance) {
        int counter = 0;
        for(Relation r : pb.targets().keySet()) {
            for(Tuple t : pb.target(r)) {
                if(!instance.tuples(r).contains(t))
                    counter++;
            }
            for(Tuple t : instance.tuples(r)) {
                if(!pb.target(r).contains(t))
                    counter++;
            }
        }
        return counter;
    }
}