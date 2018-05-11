package amalgam.eval.coverage;

import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;
import edu.mit.csail.sdg.alloy4compiler.parser.CompUtil;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Options;
import edu.mit.csail.sdg.alloy4compiler.translator.ProvenanceTraceWrapper;
import edu.mit.csail.sdg.alloy4compiler.translator.TranslateAlloyToKodkod;
import edu.mit.csail.sdg.alloy4whole.CoverageModel;
import edu.mit.csail.sdg.alloy4whole.CoverageOptions;
import edu.mit.csail.sdg.alloy4whole.CoverageStruct;
import edu.mit.csail.sdg.alloy4whole.CoverageTextLog;
import edu.mit.csail.sdg.alloy4whole.CoverageUI;

public class EvaluationCLI extends CLI {
    public static void main(String[] args) throws Err, IOException {
        if (args.length == 0) {
            System.err.println("Usage: ... <file.als>\n");
            return;
        }
        
        
        String filename = args[0];
        Map<String, List<String>> params = parse(args);
        
        String dirname = params.getOrDefault("out", Util.asList(".")).get(0);
        int timeLimit = Integer.parseInt(params.getOrDefault("time-limit", Util.asList("60")).get(0));
        String label = params.getOrDefault("label", Util.asList("")).get(0);
        String sub = params.getOrDefault("sub", Util.asList("")).get(0);
        String bound = params.getOrDefault("bound", Util.asList("")).get(0);
        
        CoverageOptions cOptS = new CoverageOptions();
        cOptS.timeLimit = 60000 * timeLimit;
        cOptS.modelLimit = -1;
        cOptS.satTrick = true;
        cOptS.inclusive = true;
        
        CoverageOptions cOptN = cOptS.dup();
        cOptN.satTrick = false;

        A4Reporter rep = new A4Reporter();
        System.out.println("=========== Parsing+Typechecking "+filename+" =============");
        Module root = CompUtil.parseEverything_fromFile(rep, null, filename);
        
        Command command = root.getAllCommands().get(Integer.parseInt(params.getOrDefault("command", Util.asList("0")).get(0)));
        System.out.println("============ Command "+command+": ============");
        
        A4Options options = new A4Options();
        options.solver = A4Options.SatSolver.MiniSatProverJNI;
        options.noOverflow = true;
        options.inferPartialInstance = false;
        options.skolemDepth = -1; // set to -1 to disable skolemization
        options.symmetry = 2000;
        
        CoverageUI cEngineN = new CoverageUI(root, null, new CoverageTextLog(), null);
        //CoverageUI cEngineB = new CoverageUI(root, null, new CoverageTextLog(), null);
        
        CoverageStruct csN = cEngineN.fromInitialSol(
                TranslateAlloyToKodkod.execute_command(rep, root.getAllReachableSigs(), command, options),
                cOptS);
        
        CoverageStruct csB = cEngineN.fromInitialSol(
                TranslateAlloyToKodkod.execute_command(rep, root.getAllReachableSigs(), command, options),
                cOptN);
        
        List<ProvenanceTraceWrapper> tN = new ArrayList<>(csN.accumTraces);
        Collections.reverse(tN);
        List<ProvenanceTraceWrapper> tB = new ArrayList<>(csB.accumTraces);
        Collections.reverse(tB);
        
        //csN.enhance(tB);
        //csB.enhance(tN);
        
        //assert csN.accumTracesSet.size() == csB.accumTracesSet.size();
        StringBuffer sb = new StringBuffer();
        PrintWriter writerN = new PrintWriter(dirname + "/normal.txt", "UTF-8");
        sb.append(label + " ");
        if ("{}".equals(sub)) {
            sb.append("& \\at{\\{\\} 3} ");
        } else {
            sb.append("& \\at{" + sub + " " + bound + "} ");
        }
        strategyPrint(csN, writerN, tB, sb, true);
        sb.append("\\rowcolor{gray!20}\n");
        sb.append("& ");
        PrintWriter writerB = new PrintWriter(dirname + "/blind.txt", "UTF-8");
        strategyPrint(csB, writerB, tN, sb, false);
        PrintWriter writerM = new PrintWriter(dirname + "/meta.txt", "UTF-8");
        writerM.println(filename);
        writerM.println(command);
        writerM.println();
        writerM.print(sb.toString());
        writerN.close();
        writerB.close();
        writerM.close();
    }

    private static void strategyPrint(CoverageStruct cs, PrintWriter writer, List<ProvenanceTraceWrapper> rest, StringBuffer sb, boolean header) throws ErrorFatal {
        for (CoverageModel m : cs.models) {
            writer.println("i = " + m.id + ", time: " + m.timeSoFar + ", prov-accum: " + m.accumNumTrace);
        }
        
        
        writer.println();
        writer.println("GC hit?: " + cs.gcHit);
        writer.println("Model all enumerated: " + cs.numAllModels);
        writer.println("Model enumeration time: " + cs.timeAll);
        writer.println("#Traces: " + cs.accumTracesSet.size());
        writer.println("Model all?: " + cs.isFinishedEnum);
        
        int allEnum = cs.numAllModels;
        int allTime = (int) cs.timeAll;
        int numTraceOrig = cs.accumTracesSet.size();
        boolean finished = cs.isFinishedEnum;
        
        
        int missing = cs.getMissing(rest);
        writer.println("Missing: " + missing);
        Queue<CoverageModel> queue = cs.getQueue();
        writer.println("#Trace-compacted: " + cs.accumTracesSet.size());
        
        int compacted = cs.accumTracesSet.size();
        sb.append("& " + compacted + " [" + missing + "] ");
        
        String msgFinished = "";
        if (!finished) {
            if (allTime < 3600) {
                msgFinished = "M";
            } else {
                msgFinished = "\\xm";
            }
        }
        
        sb.append("& " + msgFinished + " ");
        
        writer.println();
        writer.println("== Enumeration ==");
        
        printProvStat(cs.models, 50, numTraceOrig, writer, sb);
        printProvStat(cs.models, 70, numTraceOrig, writer, sb);
        printProvStat(cs.models, 90, numTraceOrig, writer, sb);
        printProvStat(cs.models, 100, numTraceOrig, writer, sb);
        
        writer.println();
        
        
        writer.println();
        writer.println("== Ensemble ==");
        printEnsemble(queue, 50, cs.accumTracesSet.size(), writer, sb);
        printEnsemble(queue, 70, cs.accumTracesSet.size(), writer, sb);
        printEnsemble(queue, 90, cs.accumTracesSet.size(), writer, sb);
        printEnsemble(queue, 100, cs.accumTracesSet.size(), writer, sb);
        
        sb.append("& " + allEnum + " ");
        if (allTime == 0) {
            sb.append("& <1 ");
        } else {
            sb.append("& " + allTime + " ");
        }
        
        sb.append("\\\\\n");
    }

    private static void printEnsemble(Queue<CoverageModel> queue, int percent, int allProv, PrintWriter writer, StringBuffer sb) {
        double numerator = allProv * percent;
        int target = (int) (numerator/100.0);
        List<CoverageModel> models = new ArrayList<>(queue);
        for (int i = 0; i < models.size(); i++) {
            CoverageModel m = models.get(i);
            if (m.queueProvCoverage >= target) {
                writer.println(percent + "%, id: " + (i + 1));
                sb.append("& " + (i + 1) + " ");
                return;
            }
        }
        return;
    }

    private static void printProvStat(List<CoverageModel> models, int percent, int allProv, PrintWriter writer, StringBuffer sb) {
        double numerator = allProv * percent;
        int target = (int) (numerator/100.0);
        for (CoverageModel m : models) {
            if (m.accumNumTrace >= target) {
                writer.println(percent + "%, time: " + m.timeSoFar + ", id: " + m.id);
                if (m.timeSoFar == 0) {
                    sb.append("& <1 [" + m.id + "] ");                    
                } else {
                    sb.append("& " + m.timeSoFar + " [" + m.id + "] ");
                }
                
                return;
            }
        }
    }
}