package amalgam.eval.provenance;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.io.UnsupportedEncodingException;
import java.lang.management.ManagementFactory;
import java.lang.management.ThreadMXBean;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import amalgam.test.TestUI;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4compiler.translator.AmalgamNaiveEvaluator;
import edu.mit.csail.sdg.alloy4compiler.translator.AmalgamVisitorHelper;
import edu.mit.csail.sdg.alloy4compiler.translator.ProvenanceTrace;
import edu.mit.csail.sdg.alloy4compiler.translator.ProvenanceTree;
import edu.mit.csail.sdg.alloy4whole.AmalgamTupleInExpr;

public class Evaluation {
    private static boolean literal = false;
    private static boolean mswenable = true;
    private static boolean useThreadTimer = true;
    private static final int NUM_ITERATIONS = 15; // for debug
    //private static final int NUM_ITERATIONS = 15; // for paper
    private static final String dir = "testing/";
    private static List<String> getSpecs() {
        List<String> specs = new ArrayList<String>();
        File[] testdir = new File(dir).listFiles();
        for (File spec : testdir) {
            if (spec.isFile()) {
                String fileName = spec.getName();
                int i = fileName.lastIndexOf('.');
                if (i > 0 && fileName.substring(i+1).equals("als")) {
                    specs.add(fileName);
                }
            }
        }
        return specs;
    }

    // Evaluation pipeline (main->run->eval)
    public static void main(String[] args) throws FileNotFoundException, UnsupportedEncodingException, InterruptedException {  
        System.out.println("Starting evaluation run for "+NUM_ITERATIONS+" iterations. AmalgamNaiveEvaluator sanity checking: "+AmalgamNaiveEvaluator.sanityCheckingExpensive);
        System.out.println("PID (for heap dumps) = "+ManagementFactory.getRuntimeMXBean().getName());
        
        /* jmap -heap:format=b,file=<file.bin> <pid> 
         * jhat <bin file> ...this may take a while to load
         */
        
        for(int i=1; i<=NUM_ITERATIONS; i++) {
            long ms = System.currentTimeMillis();            
            long exceptionCount = run(dir+"RESULTS"+i+".csv");            
            System.out.println("Iteration "+i+" had "+exceptionCount+" exceptions. Completed in "+((float)(System.currentTimeMillis()-ms))/1000+" seconds.");
            System.out.println("Number of keys in storedCaches (should be 0): "+AmalgamNaiveEvaluator.storedCaches.size());
        }
        System.exit(0);
    }
    private static long run(String out) throws FileNotFoundException, UnsupportedEncodingException, InterruptedException {
        TestUI aTestUI;
        PrintWriter writer = new PrintWriter(out, "UTF-8");
        writer.println(Data.labels());
        System.out.println("Running " + out);        
        long exceptionCount = 0;
        // for every spec
        for(String spec : getSpecs()) {            
            System.out.println("\n\nEVALUATING "+spec);            
            MemoryStopwatch modelMSW = new MemoryStopwatch(mswenable, Thread.currentThread().getId());
            // Gather results
            try {
                // load spec then run first command (ASSUME ONLY ONE COMMAND)
                aTestUI = TestUI.init(dir+spec);
                if(!aTestUI.hasCommands()) {
                    System.out.println("Skipping "+spec+"; no commands to execute.");
                    continue;
                }
                // eval first model                
                aTestUI = aTestUI.run(0);      
                if(aTestUI.currentSolution.satisfiable()) {
                    //System.err.println("Model1 = "+aTestUI.currentSolution.debugExtractKInstance());                
                    modelMSW.halt();
                    modelMSW.join();
                    System.out.println("MODEL 1 POS");
                    exceptionCount += eval(writer, aTestUI, spec, 1, modelMSW, true);
                    System.out.println("MODEL 1 NEG");
                    exceptionCount += eval(writer, aTestUI, spec, 1, modelMSW, false);
                }
                AmalgamNaiveEvaluator.storedCaches.remove(aTestUI.currentSolution);
                AmalgamVisitorHelper.clearExprCache();
                AmalgamVisitorHelper.clearResolvedCache();
                
                // eval second model
                modelMSW = new MemoryStopwatch(mswenable, Thread.currentThread().getId());
                aTestUI = aTestUI.next("diff");  
                if(aTestUI.currentSolution.satisfiable()) {
                    //System.err.println("Model2 = "+aTestUI.currentSolution.debugExtractKInstance());
                    modelMSW.halt();
                    modelMSW.join();
                    System.out.println("MODEL 2 POS");
                    exceptionCount += eval(writer, aTestUI, spec, 2, modelMSW, true);
                    System.out.println("MODEL 2 NEG");
                    exceptionCount += eval(writer, aTestUI, spec, 2, modelMSW, false);
                    aTestUI.close();
                }               
                AmalgamNaiveEvaluator.storedCaches.remove(aTestUI.currentSolution);
                AmalgamVisitorHelper.clearExprCache();
                AmalgamVisitorHelper.clearResolvedCache();
                
            } catch (Exception e) {
                modelMSW.halt();
                modelMSW.join();
                writer.println(new Data(spec, null, null, null, null, false, null, null, e.getMessage()));
                System.err.println("ERROR "+e.getMessage());
                System.err.println("------------------------------");
                e.printStackTrace();
                System.err.println("------------------------------");
            }
        }
        writer.close();
        return exceptionCount;
    }
    private static long eval(PrintWriter writer, TestUI amalgam, String spec, int modelNum, MemoryStopwatch modelMSW, boolean pos) throws Exception {
        long exceptionCount = 0;
        Set<AmalgamTupleInExpr> toTest = amalgam.getTestableTuples(pos);
        System.out.println(toTest.size()+" tuples to test with sign "+pos+"...");
        for(AmalgamTupleInExpr test : toTest) {
            //////////////////////////////
            // DEBUG
            // Sometimes the evaluator can produce different models from the GUI. 
            // In this case, we need to narrow debug output to the problematic tuple. 
            //if(!test.e.toString().contains("uctc")) continue;
            //if(!test.t.toString().contains("State$0->Switchid$1->Switchid$0")) continue;
            ////////////////////////////
            
            //System.out.println("TUPLE: "+test);
            MemoryStopwatch askMSW = new MemoryStopwatch(mswenable, Thread.currentThread().getId());
            try {
                List<ProvenanceTree> provs = amalgam.why(pos, test, literal);
                askMSW.halt();
                askMSW.join();
                writer.println(new Data(spec, modelNum, modelMSW, pos, test, true, askMSW, provs, "-"));
                //System.out.println("PASS");
            } catch (Exception e) {
                askMSW.halt();
                askMSW.join();
                writer.println(new Data(spec, modelNum, modelMSW, pos, test, false, askMSW, null, e.getMessage()));
                exceptionCount++;
                // XXX Uncomment for debugging
                System.err.println("FAIL "+e.getMessage());
                System.err.println("TUPLE "+test);
                System.err.println("------------------------------");
                e.printStackTrace();
                System.err.println("------------------------------");
                System.exit(1);
            }
         //   System.out.println("cache count: "+AmalgamNaiveEvaluator.cacheHitCountX2/2+" hits, "+AmalgamNaiveEvaluator.cacheMissCount+" misses.");
        }
        //System.gc();// DEBUG
        System.out.println("cache count: "+AmalgamNaiveEvaluator.cacheHitCountX2/2+" hits, "+AmalgamNaiveEvaluator.cacheMissCount+" misses.");
        System.out.println("Total number of NaiveEval cache entries across all "+AmalgamNaiveEvaluator.storedCaches.size()+" cached instances: "+AmalgamNaiveEvaluator.getSumCacheSize());
        System.out.println("resolvedCache entries: "+AmalgamVisitorHelper.getResolvedCacheSize()+"; tuple2ExprCache entries:"+AmalgamVisitorHelper.getExprCacheSize());        
        
        return exceptionCount;
    }

    // Helpers
    private static class MemoryStopwatch extends Thread { 
        private final long init;
        private long curr;
        private long peak = -1;
        private boolean run = false;
        private long threadID;
        private ThreadMXBean mxb;
        public MemoryStopwatch(boolean enable, long threadID) {
            super(MemoryStopwatch.class.getName());
            this.threadID = threadID;
            this.mxb = ManagementFactory.getThreadMXBean();
            if(useThreadTimer) init = mxb.getThreadCpuTime(threadID);
            else init = System.nanoTime();            

            if(enable) this.start();
        }
        public void run() {
            while(run || peak==-1) {
                if(useThreadTimer) curr = mxb.getThreadCpuTime(threadID);
                else curr = System.nanoTime();                  
                long mem = Runtime.getRuntime().totalMemory() - Runtime.getRuntime().freeMemory();
                if(peak==-1 || peak<mem) peak = mem;
            }
        }
        public void halt() {
            run = false;
        }
        public long peak() {
            return peak;
        }
        public long time() {
            return curr - init;
        }
    }
    private static class Data {
        static final String d = "\t";
        // Input
        final String spec;
        final Integer modelNum;
        final Long modelTime;
        final Long modelMem;
        final Boolean pos;
        final AmalgamTupleInExpr test;
        // Output
        final boolean pass;
        final Long askTime;
        final Long askMem;
        final List<ProvenanceTrace> provs; 
        final String info;
        // Constructor
        Data(String spec, Integer modelNum, MemoryStopwatch modelmsw, Boolean pos, AmalgamTupleInExpr test, boolean pass, MemoryStopwatch askmsw, List<ProvenanceTree> provs, String info) {
            // set data
            this.spec = spec;
            this.modelNum = modelNum;
            this.modelTime = (modelmsw==null) ? null : modelmsw.time();
            this.modelMem = (modelmsw==null) ? null : modelmsw.peak();
            this.pos = pos;
            this.test = test;
            this.pass = pass;
            this.askTime = (askmsw==null) ? null : askmsw.time();
            this.askMem = (askmsw==null) ? null : askmsw.peak();
            this.provs = new ArrayList<ProvenanceTrace>();
            if(provs!=null) for(ProvenanceTree prov : provs)
                try {
                    this.provs.add(prov.trace());
                } catch (Err e) {
                    e.printStackTrace();
                }
            this.info = info;
            /* sanity checks
                if(!this.provs.isEmpty()) {
                    if(maxTreeDepth(this.provs)<=0) throw new RuntimeException();
                    if(maxNumAlphas(this.provs)<=0) throw new RuntimeException();
                    if(maxHighlight(this.provs)<=0) throw new RuntimeException();
                }
            } catch (Exception e) {
               // throw new RuntimeException("Unclean prov data\n"+labels()+"\n"+toString());
            }*/
        }
        static String labels() {
            return "spec"+d+"modelNum"+d+"modelTime"+d+"modelMem"+d+"sign"+d+"testtuple"+d+"pass"+d+"askTime"+d+"askMem"+d+"numProvs"+d+"maxTreeDepth"+d+"maxNumAlphas"+d+"maxHighlight"+d+"info";
        }
        @Override
        public String toString() {
            return spec+d+modelNum+d+modelTime+d+modelMem+d+pos+d+test+d+pass+d+askTime+d+askMem+d+provs.size()+d+maxTreeDepth(provs)+d+maxNumAlphas(provs)+d+maxHighlight(provs)+d+info;
        }
    }
    private static int maxTreeDepth(List<ProvenanceTrace> provs) {
        int max = 0;
        for(ProvenanceTrace prov : provs) {
            int depth = prov.maxDepth();
            if(depth > max) max = depth;
        }
        return max;
    }
    private static int maxNumAlphas(List<ProvenanceTrace> provs) {
        int max = 0;
        for(ProvenanceTrace prov : provs) {
            int numAlphas = prov.uniqueAlphas().size();
            if(numAlphas > max) max = numAlphas;
        }
        return max;
    }
    private static int maxHighlight(List<ProvenanceTrace> provs) {
        int max = 0;
        for(ProvenanceTrace prov : provs) {
            int highlight = prov.maxHighlight();
            if(highlight > max) max = highlight;
        }
        return max;
    }
}
