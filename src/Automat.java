import java.util.*;
import java.math.BigInteger;
public class Automat {
    public int numStates;
    public int alphabetSize;
    public int startState;
    public Set<Integer> finalStates;

    public int[][] transition;

    public Automat(int numStates, int alphabetSize) {
        this.numStates = numStates;
        this.alphabetSize = alphabetSize;
        this.transition = new int[numStates][alphabetSize];
        this.finalStates = new HashSet<>();
    }

    public void setTransition(int state, int symbolIndex, int nextState) {
        transition[state][symbolIndex] = nextState;
    }

    public int getTransition(int state, int symbolIndex) {
        return transition[state][symbolIndex];
    }
    public Automat minimize() {
        Automat reachable = removeUnreachableStates();
        Automat minimal = reachable.hopcroftMinimize();
        return minimal.removeUnreachableStates();
    }
    private Automat removeUnreachableStates() {
        boolean[] visited = new boolean[numStates];
        Queue<Integer> queue = new LinkedList<>();

        // precislovanie zeby bol vzdy startState 0
        Map<Integer, Integer> newIndex = new HashMap<>();
        int nextId = 0;

        // Začíname od startState, ten dostane index 0
        queue.add(startState);
        visited[startState] = true;
        newIndex.put(startState, nextId++);

        // BFS
        while (!queue.isEmpty()) {
            int state = queue.poll();

            for (int c = 0; c < alphabetSize; c++) {
                int next = transition[state][c];

                if (!visited[next]) {
                    visited[next] = true;
                    newIndex.put(next, nextId++);
                    queue.add(next);
                }
            }
        }

        // Vytvoríme nový automat len s dosiahnuteľnými stavmi
        Automat result = new Automat(nextId, alphabetSize);
        result.startState = 0; // Vždy 0

        for (int oldI = 0; oldI < numStates; oldI++) {
            if (visited[oldI]) {
                int newI = newIndex.get(oldI);

                // Prenos koncovosti
                if (finalStates.contains(oldI)) {
                    result.finalStates.add(newI);
                }

                // Prenos prechodov
                for (int c = 0; c < alphabetSize; c++) {
                    int oldNext = transition[oldI][c];
                    result.transition[newI][c] = newIndex.get(oldNext);
                }
            }
        }

        return result;
    }
    public Automat hopcroftMinimize() {

        Set<Integer> finalStatesCopy = new HashSet<>(finalStates);
        Set<Integer> nonFinalStates = new HashSet<>();

        for (int i = 0; i < numStates; i++) {
            if (!finalStates.contains(i)) {
                nonFinalStates.add(i);
            }
        }
        List<Set<Integer>> P = new ArrayList<>();

        if (!finalStatesCopy.isEmpty()) {
            P.add(finalStatesCopy);
        }
        if (!nonFinalStates.isEmpty()) {
            P.add(nonFinalStates);
        }

        Queue<Set<Integer>> W = new LinkedList<>();

        if (!finalStatesCopy.isEmpty()) {
            W.add(finalStatesCopy);
        } else if (!nonFinalStates.isEmpty()) {
            W.add(nonFinalStates);
        }

        //  Hopcroft algoritmus
        while (!W.isEmpty()) {

            Set<Integer> A = W.poll();

            for (int c = 0; c < alphabetSize; c++) {

                // X = stavy, ktoré idú do A cez symbol c
                Set<Integer> X = new HashSet<>();

                for (int q = 0; q < numStates; q++) {
                    if (A.contains(transition[q][c])) {
                        X.add(q);
                    }
                }

                List<Set<Integer>> newP = new ArrayList<>();

                for (Set<Integer> Y : P) {

                    Set<Integer> intersection = new HashSet<>(Y);
                    intersection.retainAll(X);

                    Set<Integer> difference = new HashSet<>(Y);
                    difference.removeAll(X);

                    if (!intersection.isEmpty() && !difference.isEmpty()) {

                        newP.add(intersection);
                        newP.add(difference);

                        if (W.contains(Y)) {
                            W.remove(Y);
                            W.add(intersection);
                            W.add(difference);
                        } else {
                            if (intersection.size() <= difference.size()) {
                                W.add(intersection);
                            } else {
                                W.add(difference);
                            }
                        }

                    } else {
                        newP.add(Y);
                    }
                }

                P = newP;
            }
        }

        return buildMinimizedAutomat(P);
    }
    private Automat buildMinimizedAutomat(List<Set<Integer>> partitions) {

        Map<Integer, Integer> stateToGroup = new HashMap<>();

        // mapovanie starý stav → nový stav
        for (int i = 0; i < partitions.size(); i++) {
            for (int state : partitions.get(i)) {
                stateToGroup.put(state, i);
            }
        }

        Automat minimized = new Automat(partitions.size(), alphabetSize);

        // nový start state
        minimized.startState = stateToGroup.get(startState);

        // nové final states
        for (int i = 0; i < partitions.size(); i++) {
            for (int s : partitions.get(i)) {
                if (finalStates.contains(s)) {
                    minimized.finalStates.add(i);
                    break;
                }
            }
        }

        // prechody
        for (int i = 0; i < partitions.size(); i++) {

            int representative = partitions.get(i).iterator().next();

            for (int c = 0; c < alphabetSize; c++) {

                int oldTarget = transition[representative][c];
                int newTarget = stateToGroup.get(oldTarget);

                minimized.transition[i][c] = newTarget;
            }
        }

        return minimized;
    }
    public boolean accepts(int[] input) {

        int current = startState;

        for (int symbol : input) {
            current = transition[current][symbol];
        }

        return finalStates.contains(current);
    }
    public static Automat xor(Automat A, Automat B) {

        if (A.alphabetSize != B.alphabetSize) {
            throw new IllegalArgumentException("Automaty majú rozdielnu abecedu");
        }

        int newNumStates = A.numStates * B.numStates;
        int k = A.alphabetSize;

        Automat result = new Automat(newNumStates, k);

        // mapovanie (q1, q2) -> index
        // index = q1 * B.numStates + q2

        // startovaci state
        result.startState = A.startState * B.numStates + B.startState;

        // prechody
        for (int q1 = 0; q1 < A.numStates; q1++) {
            for (int q2 = 0; q2 < B.numStates; q2++) {

                int currentIndex = q1 * B.numStates + q2;

                for (int c = 0; c < k; c++) {

                    int next1 = A.transition[q1][c];
                    int next2 = B.transition[q2][c];

                    int nextIndex = next1 * B.numStates + next2;

                    result.transition[currentIndex][c] = nextIndex;
                }
            }
        }

        // finálne stavy (XOR)
        for (int q1 = 0; q1 < A.numStates; q1++) {
            for (int q2 = 0; q2 < B.numStates; q2++) {

                boolean inA = A.finalStates.contains(q1);
                boolean inB = B.finalStates.contains(q2);

                if (inA ^ inB) { // XOR
                    int index = q1 * B.numStates + q2;
                    result.finalStates.add(index);
                }
            }
        }

        return result;
    }
    // Encoder: vráti pole [n, k, a]
    public BigInteger[] encoder() {
        BigInteger n = BigInteger.valueOf(numStates);
        BigInteger k = BigInteger.valueOf(alphabetSize);
        BigInteger a = BigInteger.ZERO;

        // 1. Kódovanie prechodov (n-árna sústava)
        // Prechádzame stavy od 0 po n-1 a symboly od 0 po k-1
        for (int s = 0; s < numStates; s++) {
            for (int c = 0; c < alphabetSize; c++) {
                a = a.multiply(n).add(BigInteger.valueOf(transition[s][c]));
            }
        }

        // 2. Kódovanie koncových stavov (binárna sústava)
        // Posunieme doterajšie číslo a pridáme n bitov
        for (int s = 0; s < numStates; s++) {
            a = a.multiply(BigInteger.valueOf(2));
            if (finalStates.contains(s)) {
                a = a.add(BigInteger.ONE);
            }
        }

        return new BigInteger[]{n, k, a};
    }

    // Decoder: z n, k, a vytvorí Automat
    public static Automat decoder(BigInteger n, BigInteger k, BigInteger a) {
        int numStates = n.intValue();
        int alphabetSize = k.intValue();

        Automat result = new Automat(numStates, alphabetSize);
        result.startState = 0;

        // Dekódovanie koncových stavov
        for (int s = numStates - 1; s >= 0; s--) {
            BigInteger[] divRem = a.divideAndRemainder(BigInteger.valueOf(2));
            if (divRem[1].equals(BigInteger.ONE)) {
                result.finalStates.add(s);
            }
            a = divRem[0];
        }

        //Dekódovanie prechodov
        for (int s = numStates - 1; s >= 0; s--) {
            for (int c = alphabetSize - 1; c >= 0; c--) {
                BigInteger[] divRem = a.divideAndRemainder(n);
                result.transition[s][c] = divRem[1].intValue();
                a = divRem[0];
            }
        }

        return result;
    }

    public static List<BigInteger> generateMinimalCodes(
            int n, int alphabetSize) {

        if (n < 1 || alphabetSize < 1) {
            throw new IllegalArgumentException(
                    "Počet stavov a veľkosť abecedy musia byť kladné.");
        }

        BigInteger base = BigInteger.valueOf(n);

        // Počet všetkých kódovaní:
        // n^(n * alphabetSize) * 2^n
        BigInteger totalCodes = base.pow(n * alphabetSize)
                .multiply(BigInteger.valueOf(2).pow(n));

        List<BigInteger> minimalCodes = new ArrayList<>();

        for (BigInteger code = BigInteger.ZERO;
             code.compareTo(totalCodes) < 0;
             code = code.add(BigInteger.ONE)) {

            Automat a = Automat.decoder(
                    BigInteger.valueOf(n),
                    BigInteger.valueOf(alphabetSize),
                    code
            );

            Automat minimized = a.minimize();

            // Pôvodný automat je minimálny, ak sa
            // po minimalizácii nezmenší počet stavov.
            if (minimized.numStates == n) {
                minimalCodes.add(code);
            }
        }

        return minimalCodes;
    }

    public static void runExperiment(int m, int n) {

        int alphabetSize = 1; // Unárna abeceda {a}

        List<BigInteger> codesM =
                generateMinimalCodes(m, alphabetSize);

        List<BigInteger> codesN =
                generateMinimalCodes(n, alphabetSize);

        System.out.println("Automaty s " + m + " stavmi: "
                + codesM.size() + " minimálnych");

        System.out.println("Automaty s " + n + " stavmi: "
                + codesN.size() + " minimálnych");

        Map<Integer, BigInteger> distribution = new TreeMap<>();

        BigInteger totalXor = BigInteger.ZERO;

        for (BigInteger codeA : codesM) {

            Automat a = Automat.decoder(
                    BigInteger.valueOf(m),
                    BigInteger.valueOf(alphabetSize),
                    codeA
            );

            for (BigInteger codeB : codesN) {

                Automat b = Automat.decoder(
                        BigInteger.valueOf(n),
                        BigInteger.valueOf(alphabetSize),
                        codeB
                );

                Automat product = Automat.xor(a, b);
                Automat result = product.minimize();

                int states = result.numStates;

                distribution.merge(
                        states,
                        BigInteger.ONE,
                        BigInteger::add
                );

                totalXor = totalXor.add(BigInteger.ONE);
            }
        }

        System.out.println("\nPočet vykonaných XOR: " + totalXor);
        System.out.println("Rozdelenie podľa počtu stavov:");

        for (Map.Entry<Integer, BigInteger> entry
                : distribution.entrySet()) {

            System.out.println(
                    entry.getKey() + " stavov: "
                            + entry.getValue() + " výsledkov"
            );
        }
    }


    public static void main(String[] args) {

        Scanner scanner = new Scanner(System.in);

        System.out.print("Zadaj počet stavov prvého automatu m: ");
        int m = scanner.nextInt();

        System.out.print("Zadaj počet stavov druhého automatu n: ");
        int n = scanner.nextInt();

        runExperiment(m, n);

        scanner.close();

    }
}
