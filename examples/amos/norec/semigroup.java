package wyvern.nominal;

class XS {

  interface Semigroup<T> {
    T join(T that);
  }

  interface SumInts extends Semigroup<SumInts> {
    SumInts join(SumInts that);
    int count();
  }

  interface Pair<A extends Semigroup<A>, B extends Semigroup<B>> extends Semigroup<Pair<A, B>> {
    Pair<A, B> join(Pair<A, B> that);

    A a();
    B b();
  }

  class MkSumInts {
    SumInts mkSum(int i) {
      return new SumInts() {
        public SumInts join(SumInts that) {
          return mkSum(this.count() + that.count());
        }
        public int count() { return i; }
      };
    }
  }

  class MkPair {
    <A extends Semigroup<A>, B extends Semigroup<B>> Pair<A,B> mkPair(A a, B b) {
      return new Pair<A,B>() {

        public Pair<A, B> join(Pair<A, B> that) {
          A aa = a.join(that.a());
          B bb = b.join(that.b());
          return mkPair(aa, bb);
        }

        public A a() {
          return a;
        }
        public B b() {
          return b;
        }
      };
    }
  }
}