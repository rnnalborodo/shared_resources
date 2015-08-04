package es.upm.babel.ccjml.samples.recyclingplant.java.runenv;

import es.upm.babel.cclib.ConcIO;


/**
 * @author rnnalborodo
 */
public class  Container {
    // Max WEIGHT
    public static final int MAX_W_CONTAINER = 10000;

    private static final java.util.concurrent.locks.Lock lock = new java.util.concurrent.locks.ReentrantLock();
    private static final java.util.Random random = new java.util.Random(0);
    private static int weight = 0;

    private static boolean ready= true;

    // a load of steel has just being dropped
    private static boolean stuck = false;

    private Container() {}

    // put a new container
    public static void replace() {
        if (weight > MAX_W_CONTAINER) {
            while (true) {
                ConcIO.printfnl("ERROR: container cannot be moved. Weight = " + weight);
                try {
                    Thread.sleep(1000);
                } catch (InterruptedException x) {}
            }
        }
        ready = false;
        try {
            ConcIO.printfnl ("Retirando contenedor con peso " + weight);
            lock.lock();
            int t = random.nextInt(weight / 10);
            weight = 0;
            lock.unlock();
            Thread.sleep(t);
        } catch (InterruptedException x) {}
        if (stuck) {
            while (true) {
                ConcIO.printfnl ("ERROR: contenedor atascado por chatarra en carril.");
                try {
                    Thread.sleep(1000);
                } catch (InterruptedException x) {}
            }

        }
        ready = true;
    }

    // Incrementar el peso real en el contenedor
    public static void increment(int p) {
        boolean overweight;
        lock.lock();
        weight += p;
        overweight = weight > MAX_W_CONTAINER;
        lock.unlock();
        if (!ready) {
            stuck = true;
        }
        if (overweight) {
	    ConcIO.printfnl ("PESO LÍMITE SOBREPASADO: ¡" + weight + "!");
        }
    }
}
