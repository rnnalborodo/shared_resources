package es.upm.babel.ccjml.samples.semaphore.java;

/**
 * Semaphores are a technique for coordinating or synchronizing two activities
 * in which multiple processes compete for the same resources.
 * 
 * @author rnnalborodo
 */

public interface /* shared_resource */Semaphore {
	//@ public model instance int sem;

	//@ public instance invariant sem == 0 || sem == 1;

	//@ public initially sem == 0;

	//@ public normal_behaviour
	//@ requires true;
	//@ cond_sync sem == 0 || sem == 1;
	//@ assignable sem;
	//@ ensures sem == sem;
	//public void init(int v);

	//@ public normal_behaviour
	//@ requires true;
	// cond_sync sem == 0;
	//@ assignable sem;
  //@ ensures sem == \old(sem) +1;
	public void v();

	//@ public normal_behaviour
	//@ requires true;
	//@ cond_sync sem == 1;
	//@ assignable sem;
	//@ ensures sem == \old(sem) -1;
	public void p();

}
