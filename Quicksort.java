public class Quicksort {

    /*@ requires a != null;
      @ requires (\forall int i; (0 <= i && i < a.length) ==> a[i] <= ulimit);
      @ requires (\forall int i; (0 <= i && i < a.length) ==> llimit <= a[i]);
      @ modifies a[*];
      @ ensures (\forall int i; (0 < i && i < a.length) ==> a[i-1] <= a[i]);
      @*/
    public static void sort(int[] a, int ulimit, int llimit)
    {
        quicksort(a, 0, a.length, ulimit, llimit);
    }

  /*@ requires a != null;
    @ requires 0 <= start && start <= a.length;
    @ requires 0 <= stop && stop <= a.length;
    @ requires (\forall int i; (start <= i && i < stop) ==> a[i] <= ulimit);
    @ requires (\forall int i; (start <= i && i < stop) ==> llimit <= a[i]);
    @ modifies a[*];
    @ ensures (\forall int i; (start < i && i < stop) ==> a[i-1] <= a[i]);
    @ ensures (\forall int i; (0 <= i && i < start) ==> a[i] == \old(a[i]));
    @ ensures (\forall int i; (stop <= i && i < a.length) ==> a[i] == \old(a[i]));
    @ ensures (\forall int i; (start <= i && i < stop) ==> a[i] <= ulimit);
    @ ensures (\forall int i; (start <= i && i < stop) ==> llimit <= a[i]);
    @*/
    private static void quicksort(int[] a, int start, int stop, int ulimit, int llimit)
    {
        if (stop - start > 1) {
            int p = pivot(a, start, stop, ulimit, llimit);
            quicksort(a, start, p, a[p], llimit);
            quicksort(a, p+1, stop, ulimit, a[p]);
        }
    }

  /*@ requires a != null;
    @ requires 0 <= start;
    @ requires stop <= a.length;
    @ requires start < stop;
    @ requires (\forall int i; (start <= i && i < stop) ==> a[i] <= ulimit);
    @ requires (\forall int i; (start <= i && i < stop) ==> llimit <= a[i]);
    @ modifies a[*];
    @ ensures start <= \result;
    @ ensures \result < stop;
    @ ensures (\forall int i; (start <= i && i < \result) ==> a[i] <= a[\result]);
    @ ensures (\forall int i; (\result < i && i < stop) ==> a[\result] <= a[i]);
    @ ensures (\forall int i; (0 <= i && i < start) ==> a[i] == \old(a[i]));
    @ ensures (\forall int i; (stop <= i && i < a.length) ==> a[i] == \old(a[i]));
    @ ensures (\forall int i; (start <= i && i < stop) ==> a[i] <= ulimit);
    @ ensures (\forall int i; (start <= i && i < stop) ==> llimit <= a[i]);
    @*/
    private static int pivot(int[] a, int start, int stop, int ulimit, int llimit)
    {
        int p = partition(a, a[start], start+1, stop, ulimit, llimit);
        if (start < p)
            swap(a, start, p);
        return p;
    }

    // Write pre-conditions for this method.
    // Write post-conditions for this method.
  /*@ requires a != null;
    @ requires 0 <= start;
    @ requires stop <= a.length;
    @ requires start <= stop;
    @ requires (\forall int i; (start <= i && i < stop) ==> a[i] <= ulimit);
    @ requires (\forall int i; (start <= i && i < stop) ==> llimit <= a[i]);
    @ modifies a[*];
    @ ensures \result >= start - 1;
    @ ensures \result < stop;
    @ ensures (\forall int i; (start <= i && i <= \result) ==> a[i] <= pivot);
    @ ensures (\forall int i; (start <= i && \result < i && i < stop) ==> pivot <= a[i]);
    @ ensures (\forall int i; (0 <= i && i < start) ==> a[i] == \old(a[i]));
    @ ensures (\forall int i; (stop <= i && i < a.length) ==> a[i] == \old(a[i]));
    @ ensures (\forall int i; (start <= i && i < stop) ==> a[i] <= ulimit);
    @ ensures (\forall int i; (start <= i && i < stop) ==> llimit <= a[i]);
    @*/
    private static int partition(int[] a, int pivot, int start, int stop, int ulimit, int llimit)
    {
        if (start >= stop)
            return start - 1;
        if (a[start] < pivot)
            return partition(a, pivot, start + 1, stop, ulimit, llimit);
        if (a[--stop] > pivot)
            return partition(a, pivot, start, stop, ulimit, llimit);
        if (start < stop) {
            swap(a, start, stop);
            return partition(a, pivot, start+1, stop, ulimit, llimit);
        } else
            return start;
    }

  /*@ requires a != null;
    @ requires 0 <= i && i < a.length;
    @ requires 0 <= j && j < a.length;
    @ modifies a[i], a[j];
    @ ensures a[i] == \old(a[j]) && a[j] == \old(a[i]);
    @*/
    public static void swap(int[] a, int i, int j)
    {
        int temp = a[i];
        a[i] = a[j];
        a[j] = temp;
    }
}