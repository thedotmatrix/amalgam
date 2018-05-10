package eval.coverage;

import java.io.IOException;
import java.util.Arrays;
import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;
import edu.mit.csail.sdg.alloy4compiler.parser.CompUtil;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Options;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.mit.csail.sdg.alloy4compiler.translator.TranslateAlloyToKodkod;
import kodkod.ast.Formula;
import kodkod.engine.config.Options;
import kodkod.engine.fol2sat.Translation;
import kodkod.engine.fol2sat.Translator;
import kodkod.engine.satlab.SATFactory;
import kodkod.engine.satlab.SolverWrapper;
import kodkod.instance.Bounds;

public class AmalgamCoreCLI {
    public static void main(String[] args) throws Err, IOException {
        /*
        List<List<Integer>> input =
                Arrays.asList(Arrays.asList(1, 3, 7), Arrays.asList(1, 4), Arrays.asList(-1, 5), Arrays.asList(6));
        Set<Integer> set = new HashSet(Arrays.asList(1, 3, 4, 5, 6, 7));
        System.out.println(AmalgamCoreHelper.getLNClauses(new CNF(input), set));
        */
        
        if (args.length == 0) {
            System.err.println("Usage: ... <file.als>");
            return;
        }
        String filename = args[0];
                
        A4Reporter rep = new A4Reporter();
        Module root = CompUtil.parseEverything_fromFile(rep, null, filename);
        
        Command command = root.getAllCommands().get(0);
        
        A4Options options = new A4Options();
        options.solver = A4Options.SatSolver.MiniSatProverJNI;
        A4Solution ans = TranslateAlloyToKodkod.execute_command(rep, root.getAllReachableSigs(), command, options);
        Bounds b = ans.getBounds();

        Options realOptions = new Options();
        realOptions.setSolver(SATFactory.MiniSatProver);
        
        Translation.Whole translation = Translator.translate(Formula.TRUE, b, realOptions);             
        //final long endTransl = System.currentTimeMillis();
        SolverWrapper solver = new SolverWrapper(realOptions, translation.cnf());
        solver.addVariables(1);
        int var = solver.numberOfVariables();
        Integer t = solver.registerClauses(Arrays.asList(Arrays.asList(var), Arrays.asList(-var)));
        if (!solver.solveAndAssume(Arrays.asList(-t))) {
            System.out.println("a");
            System.out.println(solver.solveAndAssume(Arrays.asList(-t)));
            System.out.println("b");
            System.out.println(solver.proof().core());
            System.out.println("c");
            System.out.println(solver.solveAndAssume(Arrays.asList(-t)));
            System.out.println("d");
        }
        
    }
}


