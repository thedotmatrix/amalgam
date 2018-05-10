package edu.mit.csail.sdg.alloy4whole;

public class CoverageOptions {
    public long timeLimit;
    public int modelLimit;
    public boolean showProv;
    public boolean satTrick;
    public boolean inclusive;
    
    public CoverageOptions() {
        timeLimit = -1;
        modelLimit = -1;
        showProv = true;
        satTrick = false;
        inclusive = true;
    }
    
    public CoverageOptions dup() {
        CoverageOptions ret = new CoverageOptions();
        ret.timeLimit = timeLimit;
        ret.modelLimit = modelLimit;
        ret.showProv = showProv;
        ret.satTrick = satTrick;
        ret.inclusive = inclusive;
        return ret;
    }
}
