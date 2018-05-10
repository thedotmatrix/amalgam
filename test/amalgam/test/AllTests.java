package amalgam.test;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;

import amalgam.test.sat.SolverExtensionTest;
import amalgam.test.sys.AllSysTests;
import amalgam.test.unit.AllUnitTests;

@RunWith(Suite.class)
@SuiteClasses({
	SolverExtensionTest.class,
	AllUnitTests.class,
	AllSysTests.class
})

public class AllTests {}
