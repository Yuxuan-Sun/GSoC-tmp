#!/usr/bin/env python
# coding: utf-8

r"""
# Finite double posets

This class implements finite double posets, i.e., finite sets
equipped with two (unrelated) partial orders.

Notation used in the definitions follows mainly [MalReu95]_.

REFERENCES:

.. [MalReu95] \Claudia Malvenuto, Christophe Reutenauer, *A self paired Hopf algebra on double posets and a Littlewood–Richardson rule*, Journal of Combinatorial Theory, Series A
Volume 118, Issue 4, May 2011, pp. 1322--1333, https://doi.org/10.1016/j.jcta.2010.10.010 .

"""

from sage.categories.hopf_algebras import HopfAlgebras
from sage.combinat.posets.posets import FinitePoset
from sage.combinat.skew_partition import SkewPartitions
from sage.combinat.partition import Partitions
from sage.categories.finite_posets import FinitePosets
from sage.combinat.posets.elements import PosetElement
from itertools import permutations, product
from sage.structure.element import Element

class DoublePoset(Parent, UniqueRepresentation):
    r"""
    A (finite) double poset.

    This means a finite set `E` equipped with two
    partial orders `\leq_1` and `\leq_2`.
    See [MalReu95]_.

    INPUT:
    - ``P1`` -- either a list of covering relations or a Sage ``Poset``
                defining the first order `\leq_1`
    - ``P2`` -- likewise, defines the second order `\leq_2`
    - ``elements`` -- (optional) ordered list of all elements
                      of the ground set;
                      by default, taken to be the ground set of ``P1``

    OUTPUT:

    ``DoublePoset`` -- an instance of the
    :class:`DoublePoset` class.

    If ``category`` is specified, then the poset is created in this
    category instead of :class:`DoublePosets`.

    .. TODO::

        We don't have a category yet.

    EXAMPLES::

        sage: D = DoublePoset(Poset([[1,2,3,4],[[1,2],[2,4],[1,3],[3,4]]]), Poset([[1,2,3,4],[[2,3]]]))
        sage: D
        Finite double poset containing 4 elements
        sage: D.leq(2, 2, 3)   # 2 <=_2 3 is true
        True
        sage: D.leq(2, 1, 3)   # 1 <=_2 3 is false
        False
        sage: D.leq(1, 1, 4)   # 1 <=_1 4 is true
        True
        sage: D.leq(1, 2, 3)   # 2 <=_1 3 is false
        False
        sage: D.poset(1)
        Finite poset containing 4 elements
        sage: D.poset(1).relations()
        [[1, 1], [1, 2], [1, 3], [1, 4], [2, 2], [2, 4], [3, 3], [3, 4], [4, 4]]
        sage: D.poset(2)
        Finite poset containing 4 elements
        sage: D.poset(2).relations()
        [[4, 4], [2, 2], [2, 3], [3, 3], [1, 1]]
        sage: sorted(D.elements())
        [1, 2, 3, 4]
        sage: bool(D)
        True

        sage: D = DoublePoset([(1,2)], [(1,3)], elements=[1,2,3])
        sage: D.elements()
        {1, 2, 3}
        sage: D.leq(1, 1, 2)   # 1 <=_1 2
        True
        sage: D.leq(2, 1, 3)   # 1 <=_2 3
        True
        sage: D.poset(1).cover_relations()
        [(1, 2)]
        sage: D.poset(2).cover_relations()
        [(1, 3)]

    TESTS::

        sage: D = DoublePoset(Poset(), Poset())
        sage: D
        Finite double poset containing 0 elements
        sage: D.elements()
        set()
        sage: D.poset(1)
        Finite poset containing 0 elements
        sage: bool(D)
        False

    """
    @staticmethod
    def __classcall__(cls, P1, P2, elements=None, category=None):
        """
        Normalize the arguments passed to the constructor.

        INPUT:

        - ``P1`` -- a finite poset `P_1`;
        - ``P2`` -- a finite poset `P_2`, required to equal
          `P_1` as a set
        """
        if P1 not in FinitePosets:
            if elements is None:
                # take the elements that appear in P1
                elements = tuple([x for pair in P1 for x in pair])
            P1 = Poset((elements, P1))
        if P2 not in FinitePosets:
            P2 = Poset((elements, P2))
        return super().__classcall__(cls, P1, P2,
                                     category=category)

    def __init__(self, P1, P2, category) -> None:
        r"""

        TESTS::

            sage: D = DoublePoset(Poset([[1,2,3,4],[[1,2],[2,4],[1,3],[3,4]]]), Poset([[1,2,3,4],[[2,3]]]))
            sage: TestSuite(D).run()

        See also the extensive tests in the class documentation.
        """
        Parent.__init__(self, category=category, facade=True)
        self._P1 = P1
        self._P2 = P2
        self._elements = list(P1)

    def _repr_(self) -> str:
        r"""
        Return a string representation of this finite double poset.

        TESTS::

            sage: D = DoublePoset([(1,2)], [(1,3)], elements=[1,2,3])
            sage: repr(D)
            'Finite double poset containing 3 elements'

            sage: D = DoublePoset([], [], elements=[])
            sage: repr(D)
            'Finite double poset containing 0 elements'
        """
        return "Finite double poset containing " + str(len(self.elements())) + " elements"

    def __len__(self):
        r"""
        Return the number of elements of this double poset.

        TESTS::

            sage: D = DoublePoset([(1,2)], [(1,3)], elements=[1,2,3,4,5])
            sage: len(D)
            5
        """
        return self._P1.cardinality()

    def elements(self):
        r"""
        Return the elements of this double poset.

        TESTS::

            sage: D = DoublePoset([(1,2)], [(1,3)], elements=[1,2,3,4,5])
            sage: sorted(D.elements())
            [1, 2, 3, 4, 5]
        """
        return set(self._P1)

    base_set = elements
    base_set_cardinality = __len__
    size = __len__

    def __iter__(self):
        r"""
        Iterate over this double poset.

        TESTS::

            sage: D = DoublePoset([(1,2)], [(1,3)], elements=[1,2,3,4,5])
            sage: sorted([i for i in D])
            [1, 2, 3, 4, 5]
        """
        return self._P1.__iter__()

    def __getitem__(self, i):
        r"""
        Return the `i`-th element of the double poset, according to the
        ordering of the underlying first poset.

        TESTS::

            sage: D = DoublePoset([(1,2)], [(1,3)], elements=[1,2,3])
            sage: [D[0],D[1],D[2]]
            [3, 1, 2]
        """
        return self._P1.__getitem__(i)

    def an_element(self):
        r'''
        Return an element of ``self``.

        TESTS::

            sage: D = DoublePoset([(1,2)], [(1,3)], elements=[1,2,3])
            sage: D.an_element()
            3
        '''
        return list(self)[0]

    def __bool__(self) -> bool:
        r"""
        Return if ``self`` is empty or not.

        EXAMPLES::

            sage: D = DoublePoset([(1,2)], [(1,3)], elements=[1,2,3])
            sage: bool(D)
            True
            sage: D0 = DoublePoset([], [], elements=[])
            sage: bool(D0)
            False
        """
        return bool(self._elements)

    def __contains__(self, x) -> bool:
        r"""
        Return ``True`` if ``x`` is an element of the double poset.

        TESTS::

            sage: from sage.combinat.posets.posets import FinitePoset
            sage: P5 = FinitePoset(DiGraph({(5,):[(4,1),(3,2)],
            ....:   (4,1):[(3,1,1),(2,2,1)],
            ....:   (3,2):[(3,1,1),(2,2,1)],
            ....:   (3,1,1):[(2,1,1,1)],
            ....:   (2,2,1):[(2,1,1,1)],
            ....:   (2,1,1,1):[(1,1,1,1,1)],
            ....:   (1,1,1,1,1):[]}))
            sage: x = P5.list()[3]
            sage: D = DoublePoset(P5, P5)
            sage: x in D
            True
            sage: 3 in D
            False
        """
        return x in self._elements

    is_parent_of = __contains__

    def poset(self, i):
        r"""
        Return the underlying set of ``self``,
        equipped with the first order `\leq_1` if
        ``i = 1`` and with the second order `\leq_2`
        if ``i = 2``.

        EXAMPLES::

            sage: D = DoublePoset(Poset([[1,2],[[1,2]]]), Poset([[1,2],[]]))
            sage: D.poset(1).relations()
            [[1, 1], [1, 2], [2, 2]]
            sage: D.poset(2).relations()
            [[2, 2], [1, 1]]
        """
        if i == 1:
            return self._P1
        else:
            return self._P2

    def is_lequal(self, i, a, b):
        r"""
        Check if `a \leq_i b`, where `a` and `b`
        are two elements of ``self``, and where
        `i` is either 1 or 2.

        EXAMPLES::

            sage: D = DoublePoset(Poset([[1,2],[[1,2]]]), Poset([[1,2],[]]))
            sage: D.is_lequal(1, 1, 2)
            True
            sage: D.is_lequal(1, 1, 1)
            True
            sage: D.is_lequal(1, 2, 1)
            False
            sage: D.is_lequal(2, 1, 2)
            False
            sage: D.is_lequal(2, 1, 1)
            True
        """
        return self.poset(i).is_lequal(a, b)

    leq = is_lequal

    def is_less_than(self, i, a, b):
        r"""
        TODO
        """
        return self.poset(i).is_less_than(a, b)

    lt = is_less_than

    def is_gequal(self, i, a, b):
        r"""
        TODO
        """
        return self.poset(i).is_gequal(a, b)

    geq = is_gequal

    def is_greater_than(self, i, a, b):
        r"""
        TODO
        """
        return self.poset(i).is_greater_than(a, b)

    gt = is_greater_than

    def relabel(self, relabeling=None):
        r"""
        Relabel ``self`` using the relabeling
        function/dictionary ``relabeling``.

        See :meth:`FinitePoset.relabel` for the
        allowed syntax.

        EXAMPLES::

            sage: D = DoublePoset(Poset([[3,5,7], [[5,7], [7,3]]]), Poset([[3,5,7], [[3,5]]]))
            sage: D.poset(1).cover_relations()
            [[5, 7], [7, 3]]
            sage: D.poset(2).cover_relations()
            [[3, 5]]
            sage: E = D.relabel(relabeling=lambda x: x + 1)
            sage: sorted(E.elements())
            [4, 6, 8]
            sage: E.poset(1).cover_relations()
            [[6, 8], [8, 4]]
            sage: E.poset(2).cover_relations()
            [[4, 6]]
        """
        Q1 = self._P1.relabel(relabeling=relabeling)
        Q2 = self._P2.relabel(relabeling=relabeling)
        elementsQ = list(Q1)
        return DoublePoset(Q1, Q2)

    def standardization(self):
        r"""
        Relabel ``self`` so that the elements of
        ``self`` (in their Python order) become
        `1, 2, \ldots, n`.

        EXAMPLES::

            sage: D = DoublePoset(Poset([[3,5,7], [[5,7], [7,3]]]), Poset([[3,5,7], [[3,5]]]))
            sage: D.poset(1).cover_relations()
            [[5, 7], [7, 3]]
            sage: D.poset(2).cover_relations()
            [[3, 5]]
            sage: E = D.standardization()
            sage: sorted(E.elements())
            [1, 2, 3]
            sage: E.poset(1).cover_relations()
            [[2, 3], [3, 1]]
            sage: E.poset(2).cover_relations()
            [[1, 2]]
        """
        els = sorted(self.elements())
        standardize = {elsi: i+1 for (i, elsi) in enumerate(els)}
        return self.relabel(relabeling=standardize)

    # To multiply two basis elements x and y in the
    # Hopf algebra, take
    # x.compose(y, relabel=True).standardization()
    # or
    # x.compose(y, relabel=True, standardize=True) if you implement this

    def compose(self, other, relabel=False):
        r"""
        Return the composition of two double posets as
        defined in [MalReu95]_.

        This requires the ground sets to be disjoint.
        Unless the ``relabel`` parameter is set to
        ``True``, in which case each element `x` of
        ``self`` is relabelled as ``(1, x)`` whereas
        each element ``y`` of ``other`` is relabelled
        as ``(2, y)``.

        Let ``self`` `= (E, <_1, <_2)` and
        ``other`` `= (F, <_1, <_2)`.
        The composition is a new double poset
        `EF = (E \cup F, <_1', <_2')` where:
        - `<_1'` is the disjoint union of the first orders of `E` and `F`;
        - `<_2'` is the ordinal sum: it contains all of second orders of `E` and `F`,
            and for every `e \in E` and `f \in F`, we set `e <_2' f`.

        INPUT:

        - ``other`` -- another ``DoublePoset`` to compose with ``self``;
        - ``relabel`` (boolean, default: ``False``) --
        if ``True``, then each element `x` of
        ``self`` is relabelled as ``(1, x)`` whereas
        each element ``y`` of ``other`` is relabelled
        as ``(2, y)``.

        OUTPUT:

        - A new ``DoublePoset`` representing the composition of ``self`` and ``other``.

        EXAMPLES::

            sage: D1 = DoublePoset([(1,2), (1,3)], [(2,3)], elements=[1,2,3])
            sage: D2 = DoublePoset([(4,5)], [(4,5), (5,6)], elements=[4,5,6])
            sage: D = D1.compose(D2)
            sage: sorted(D.elements())
            [1, 2, 3, 4, 5, 6]

            sage: sorted(D.poset(1).cover_relations())
            [[1, 2], [1, 3], [4, 5]]

            sage: sorted(D.poset(2).cover_relations())
            [[1, 4], [2, 3], [3, 4], [4, 5], [5, 6]]

            sage: D1 = DoublePoset([(1,2)], [(2,3)], elements=[1,2,3])
            sage: D2 = DoublePoset([], [(1,2),(1,3)], elements=[1,2,3])
            sage: D = D1.compose(D2, relabel=True)
            sage: sorted(D.elements())
            [(1, 1), (1, 2), (1, 3), (2, 1), (2, 2), (2, 3)]

            sage: sorted(D.poset(1).cover_relations())
            [[(1, 1), (1, 2)]]

            sage: sorted(D.poset(2).cover_relations())
            [[(1, 1), (2, 1)], [(1, 2), (1, 3)], [(1, 3), (2, 1)],
            [(2, 1), (2, 2)], [(2, 1), (2, 3)]]

        """
        if relabel:
            E = self.relabel(relabeling=lambda x: (1, x))
            F = other.relabel(relabeling=lambda y: (2, y))
        else:
            E = self
            F = other

        E1 = E.poset(1)
        F1 = F.poset(1)
        E2 = E.poset(2)
        F2 = F.poset(2)

        # check: disjoint ground sets
        EF_elements = list(E1) + list(F1)
        if len(set(EF_elements)) != len(EF_elements):
            raise ValueError("Double posets must be disjoint for doing compsition")

        # First order: disjoint union
        rel1 = list(E1.cover_relations()) + list(F1.cover_relations())

        # Second order: ordinal sum
        rel2 = list(E2.cover_relations()) + list(F2.cover_relations())
        for e in E2:
            for f in F2:
                rel2.append((e, f))

        return DoublePoset(rel1, rel2, elements=EF_elements)

    def decompositions_iter(self):
        """
        Iterate over all decompositions of this double poset
        as pairs of double posets.

        See :meth:`decompositions`.
        """
        P1 = self.poset(1)
        P2 = self.poset(2)
        ground_set = set(self.elements())

        for I in P1.order_ideals_lattice():
            I = set(I)
            S = ground_set - I

            # Induce subposets
            P1_I = P1.subposet(I)
            P2_I = P2.subposet(I)
            P1_S = P1.subposet(S)
            P2_S = P2.subposet(S)

            D_I = DoublePoset(P1_I.cover_relations(),
                              P2_I.cover_relations(),
                              elements=list(I))
            D_S = DoublePoset(P1_S.cover_relations(),
                              P2_S.cover_relations(),
                              elements=list(S))
            yield (D_I, D_S)

    def decompositions(self):
        r"""
        Return all decompositions of this double poset as
        pairs of double posets.

        A decomposition of a double poset `(E, <_1, <_2)` is a pair `(I, S)` such that:
          - `I` is an **inferior ideal** (order ideal) of the first order `<_1`;
          - `S = E \setminus I` is its complement;
          - both `I` and `S` inherit their orders `<_1` and `<_2` from `E`.

        This function returns all such decompositions, each as a pair of ``DoublePoset``s.

        OUTPUT:

        - A list of pairs `(I, S)` where `I` and `S` are ``DoublePoset`` instances.

        EXAMPLES::

            sage: D = DoublePoset([(1,2),(2,3)], [(1,3)], elements=[1,2,3])
            sage: decs = D.decompositions()
            sage: for I, S in decs:
            ....:     print(sorted(I.elements()), "|", sorted(S.elements()))
            [] | [1, 2, 3]
            [1] | [2, 3]
            [1, 2] | [3]
            [1, 2, 3] | []

            sage: D = DoublePoset([(1,2),(1,3)], [(1,3)], elements=[1,2,3])
            sage: decs = D.decompositions()
            sage: for I, S in decs:
            ....:     print(sorted(I.elements()), "|", sorted(S.elements()))
            [] | [1, 2, 3]
            [1] | [2, 3]
            [1, 2] | [3]
            [1, 3] | [2]
            [1, 2, 3] | []
        """
        return list(self.decompositions_iter())

    def flip(self):
        r"""
        Return the flipped version of the double poset
        ``self``. This is obtained from ``self`` by
        switching the roles of first and second order.

        EXAMPLES::

            sage: D = DoublePoset([(1,2),(2,3)], [(1,3)], elements=[1,2,3])
            sage: D.flip()
            Finite double poset containing 3 elements
            sage: D.flip().poset(1).relations()
            [[2, 2], [1, 1], [1, 3], [3, 3]]
            sage: D.flip().poset(2).relations()
            [[1, 1], [1, 2], [1, 3], [2, 2], [2, 3], [3, 3]]
            sage: D.flip().flip() == D
            True
            sage: D.flip() == D
            False
        """
        return DoublePoset(self._P2,
                                 self._P1)

    def pictures_iter(self, other):
        r"""
        Iterate over the pictures `\phi` from the double
        poset ``self`` to another double poset ``other``.
        The pictures are encoded as dictionaries
        `\{e: \phi(e)\}`.

        See :meth:`pictures`.
        """
        D1 = self
        D2 = other
        E = list(D1.elements())
        F = list(D2.elements())

        if len(E) != len(F):
            return

        n = len(E)
        count = 0

        # get all bijections
        for sigma in permutations(range(n)):
            phi = {E[i]: F[sigma[i]] for i in range(n)}
            phi_inv = {v: k for k, v in phi.items()}

            # Forward: e <_1 e′ => phi(e) <_2 phi(e′)
            forward_fail = any(
                D1.leq(1, e1, e2) and not D2.leq(2, phi[e1], phi[e2])
                for e1 in E for e2 in E if e1 != e2
            )

            if forward_fail:
                continue

            # Backward: f <_1 f′ => phi_invs(f) <_2 phi_invs(f′)
            backward_fail = any(
                D2.leq(1, f1, f2) and not D1.leq(2, phi_inv[f1], phi_inv[f2])
                for f1 in F for f2 in F if f1 != f2
            )

            if not backward_fail:
                yield phi

    def pictures(self, other):
        r"""
        Return a list of all pictures `\phi` from the double
        poset ``self`` to another double poset ``other``.
        The pictures are encoded as dictionaries
        `\{e: \phi(e)\}`.

        A **picture** from a double poset `(E, \leq_1, \leq_2)` to
        `(F, \leq_1, \leq_2)` is a bijection `\phi: E \to F` such that:

        - if `e \leq_1 e'` in ``self``, then `\phi(e) \leq_2 \phi(e')` in ``other``;
        - if `f \leq_1 f'` in ``other``, then `\phi^{-1}(f) \leq_2 \phi^{-1}(f')` in ``self``.

        INPUT:

        - ``other`` -- a second ``DoublePoset`` with the same number of elements.

        OUTPUT:

        - A list of bijections (Python dicts) representing all valid pictures
          from ``self`` to ``other``.

        EXAMPLES::

            sage: E = DoublePoset([(1,2)], [(1,2)], elements=[1,2])
            sage: F = DoublePoset([(3,4)], [(3,4)], elements=[3,4])
            sage: E.pictures(F)
            [{1: 3, 2: 4}, {1: 4, 2: 3}]

            sage: E = DoublePoset([(1,3), (2,3)], [(1,2), (2,3)], elements=[1,2,3])
            sage: F = DoublePoset([(4,6), (5,6)], [(4,5), (5,6)], elements=[4,5,6])
            sage: E.pictures(F)
            [{1: 4, 2: 5, 3: 6}, {1: 5, 2: 4, 3: 6}]

            sage: E = DoublePoset([(1,2)], [(1,2), (2,3)], elements=[1,2,3])
            sage: F = DoublePoset([(4,5), (5,6)], [(4,6)], elements=[4,5,6])
            sage: E.pictures(F)
            []

        TESTS:

        There are no pictures between double posets of
        different sizes::

            sage: E = DoublePoset([(1,2)], [(1,2)], elements=[1,2])
            sage: F = DoublePoset([], [], elements=[1])
            sage: E.pictures(F)
            []
            sage: F.pictures(E)
            []
        """
        return list(self.pictures_iter(other))

    def number_of_pictures(self, other):
        r"""
        Return the number of all pictures `\phi` from the
        double poset ``self`` to another double poset ``other``.

        EXAMPLES::

            sage: E = DoublePoset([(1,2)], [(1,2), (2,3)], elements=[1,2,3])
            sage: F = DoublePoset([(4,5), (5,6)], [(4,6)], elements=[4,5,6])
            sage: E.number_of_pictures(F)
            0
            sage: E = DoublePoset([(1,2)], [(1,2)], elements=[1,2])
            sage: F = DoublePoset([(3,4)], [(3,4)], elements=[3,4])
            sage: E.number_of_pictures(F)
            1
        """
        return sum(1 for _ in self.pictures_iter(other))

    def isomorphisms_iter(self, other):
        r"""
        Iterate over the isomorphisms `\phi` from the double
        poset ``self`` to another double poset ``other``.
        The isomorphisms are encoded as dictionaries
        `\{e: \phi(e)\}`.

        See :meth:`isomorphisms`.
        """
        D1 = self
        D2 = other
        E = list(D1.elements())
        F = list(D2.elements())

        if len(E) != len(F):
            return

        n = len(E)
        count = 0

        # get all bijections
        for sigma in permutations(range(n)):
            phi = {E[i]: F[sigma[i]] for i in range(n)}

            # Isomorphism of first orders
            forward_fail = any(
                D1.leq(1, e1, e2) != D2.leq(1, phi[e1], phi[e2])
                for e1 in E for e2 in E if e1 != e2
            )

            if forward_fail:
                continue

            # Isomorphism of second orders
            backward_fail = any(
                D1.leq(2, e1, e2) != D2.leq(2, phi[e1], phi[e2])
                for e1 in E for e2 in E if e1 != e2
            )

            if not backward_fail:
                yield phi

    def isomorphisms(self, other):
        r"""
        Return a list of all isomorphisms `\phi` from the double
        poset ``self`` to another double poset ``other``.
        The isomorphisms are encoded as dictionaries
        `\{e: \phi(e)\}`.

        An **isomorphism** between two double posets
        `(E, \leq_1, \leq_2)` and `(F, \leq_1, \leq_2)` is a bijection
        `\phi: E \to F` such that:

        - for all`$e, e' \in E`,
          `\phi(e) \leq_1 \phi(e')` in ``other`` if and only if `e \leq_1 e'` in ``self``;
        - for all $e, e' \in E$,
          `\phi(e) \leq_2 \phi(e')` in ``other`` if and only if `e \leq_2 e'` in ``self``.

        INPUT:

        - ``other`` -- a second ``DoublePoset`` with the same number of elements.

        OUTPUT:

        - A list of bijections representing all isomorphisms between ``self`` and ``other``.

        EXAMPLES::

            sage: D1 = DoublePoset([(1,2)], [(1,2)], elements=[1,2])
            sage: D2 = DoublePoset([(3,4)], [(3,4)], elements=[3,4])
            sage: D1.isomorphisms(D2)
            [{1: 3, 2: 4}]

            sage: Y = Poset([[1,2,3,4], [[1,2], [2,3], [2,4]]])
            sage: D = DoublePoset(Y, Y)
            sage: D.isomorphisms(D)
            [{1: 1, 2: 2, 3: 3, 4: 4}, {1: 1, 2: 2, 3: 4, 4: 3}]
            sage: P = Poset([[1,2,3,4], [[1,2], [2,3], [3,4]]])
            sage: E = DoublePoset(Y, P)
            sage: E.isomorphisms(E)
            [{1: 1, 2: 2, 3: 3, 4: 4}]
        """
        return list(self.isomorphisms_iter(other))

    def number_of_isomorphisms(self, other):
        r"""
        Return the number of all isomorphisms `\phi` from the
        double poset ``self`` to another double poset ``other``.

        EXAMPLES::

            TODO.
        """
        return sum(1 for _ in self.isomorphisms_iter(other))

    def is_isomorphic(self, other):
        r"""
        Return whether the double poset ``self`` is
        isomorphic to another double poset ``other``.

        EXAMPLES::

            sage: P = Poset([[1,2],[(1,2)]])
            sage: Q = Poset([[1,2],[(2,1)]])
            sage: D = DoublePoset(P, P)
            sage: E = DoublePoset(Q, Q)
            sage: F = DoublePoset(P, Q)
            sage: D.is_isomorphic(E)
            True
            sage: D.is_isomorphic(F)
            False
        """
        return any(True for _ in self.isomorphisms_iter(other))

    def pi_partitions_iter(self, bound):
        r"""
        Iterate over all `\pi`-partitions x: E -> {1, ..., bound} for this double poset.

        The `\pi`-partitions are encoded as dictionaries.

        A map x is a `\pi`-partition if:
            - e <_1 e'               => x(e) <= x(e')
            - e <_1 e' and e >=_2 e' => x(e) < x(e')

        INPUT:
            - bound: positive integer N, values of x are in {1,...,N}
        """
        E = list(self)

        for values in product(range(1, bound+1), repeat=len(E)):
            x = dict(zip(E, values))
            valid = True
            for e1 in E:
                for e2 in E:
                    if e1 == e2:
                        continue
                    if self.leq(1, e1, e2):
                        if x[e1] > x[e2]:
                            valid = False
                            break
                        if self.geq(2, e1, e2) and x[e1] == x[e2]:
                            valid = False
                            break
                if not valid:
                    break
            if valid:
                yield x

    def pi_partitions(self, bound):
        r"""
        Return a list of all `\pi`-partitions
        `x : E \to \{1, ..., b\}` for this double poset,
        where `b` is the integer ``bound``.

        The `\pi`-partitions are encoded as dictionaries.

        EXAMPLES::

            sage: D = DoublePoset([(1,2)], [(2,1)], elements=[1,2])
            sage: D.pi_partitions(3)
            [{1: 1, 2: 2}, {1: 1, 2: 3}, {1: 2, 2: 3}]

            TODO: More examples.
        """
        return list(self.pi_partitions_iter(bound))

    def graph(self, other, phi):
        r"""
        Return the graph of two double posets
        ``self`` and ``other`` given a bijection ``phi``.

        If ``self`` is `E` and ``other`` is `F`, and if ``phi`` is a
        bijection `\phi : E \to F`, then this is
        `E \times_\phi F`.

        The bijection phi should be given as a
        dictionary `\{e: \phi(e)\}`.

        TODO: Examples.
        # E.graph(F, {1:3, 2:4}).poset(1).cover_relations()
        """
        D1 = self
        D2 = other
        E = D1.elements()
        F = D2.elements()

        elements = [(e, phi[e]) for e in E]
        cov1 = []
        cov2 = []

        # first order: (e, f) <_1 (e', f') iff f <_1 f' in D2
        for (e1, f1) in elements:
            for (e2, f2) in elements:
                if f1 != f2 and D2.leq(1, f1, f2):
                    cov1.append(((e1,f1),(e2,f2)))

        # second order: (e, f) <_2 (e', f') iff e <_2 e' in D1
        for (e1, f1) in elements:
            for (e2, f2) in elements:
                if e1 != e2 and D1.leq(2, e1, e2):
                    cov2.append(((e1,f1),(e2,f2)))

        D_phi = DoublePoset(cov1, cov2, elements=elements)

        return D_phi





def internal_product_helper(D1, D2):
    r"""
    Iterate over all D1 x_phi D2 for all increasing bijections phi
    (the internal product = the sum of these)
    """

    E = D1.elements()
    F = D2.elements()

    if len(E) != len(F):
        return

    n = len(E)
    results = []

    for sigma in permutations(range(n)):
        phi = {E[i]: F[sigma[i]] for i in range(n)}

        # Check increasing
        increasing_fail = any(
            D1.leq(1, e1, e2) and not D2.leq(2, phi[e1], phi[e2])
            for e1 in E for e2 in E if e1 != e2
        )

        if increasing_fail:
            continue

        D_phi = D1.graph(D2, phi)
        yield D_phi

def DiagramDoublePoset(D, partition=False):
    r"""
    The double poset corresponding to a diagram
    `D \subseteq \mathbb{Z} \times \mathbb{Z}`.
    The first order is given by
    `(i, j) \leq_1 (u, v) \iff
    i \leq u \text{ and } j \leq v`.
    The second order is given by
    `(i, j) \leq_2 (u, v) \iff
    i \leq u \text{ and } j \geq v`.
    Note that this is not quite the `E_\nu` from
    [MalReu95]_.

    The diagram `D` can be provided as an
    iterable consisting of pairs `(i, j)`, or,
    if a skew Young diagram is desired, as a
    skew partition (:class:`SkewPartition`).
    In the latter case, the optional parameter
    ``partition`` must be set to ``True``.

    EXAMPLES::

        sage: D = DiagramDoublePoset([[3,3],[1]], partition=True)
        sage: D
        Finite double poset containing 5 elements
        sage: sorted(D.elements())
        [(0, 1), (0, 2), (1, 0), (1, 1), (1, 2)]
        sage: D.poset(1).cover_relations()
        [[(1, 0), (1, 1)],
         [(0, 1), (0, 2)],
         [(0, 1), (1, 1)],
         [(0, 2), (1, 2)],
         [(1, 1), (1, 2)]]
        sage: D.poset(2).cover_relations()
        [[(0, 2), (1, 2)],
         [(0, 2), (0, 1)],
         [(1, 2), (1, 1)],
         [(0, 1), (1, 1)],
         [(1, 1), (1, 0)]]

    We check the result from [MalReu95]_ that the
    number of pictures between the double posets of
    two skew Young diagrams is the corresponding
    Littlewood–Richardson coefficient (i.e., Hall
    inner product of the respective skew Schur
    functions)::

        sage: def num_pics(lam, mu):
        ....:     Dlam = DiagramDoublePoset(lam, partition=True)
        ....:     Dmu = DiagramDoublePoset(mu, partition=True)
        ....:     return Dlam.number_of_pictures(Dmu)
        sage: def lrcoeff(lam, mu):
        ....:     Sym = SymmetricFunctions(QQ)
        ....:     s = Sym.s()
        ....:     return s(lam).scalar(s(mu))
        sage: all(num_pics(lam, mu) == lrcoeff(lam, mu)
        ....:        for lam in SkewPartitions(4)
        ....:        for mu in SkewPartitions(4)) # long time
        True
    """
    if partition:
        cells = SkewPartition(D).cells()
    else:
        cells = list(set(D))
    rel1 = [(c, d) for c in cells for d in cells
            if c[0] <= d[0] and c[1] <= d[1]]
    rel2 = [(c, d) for c in cells for d in cells
            if c[0] <= d[0] and c[1] >= d[1]]
    return DoublePoset(rel1, rel2, elements=cells)

def check_LR(n):
    # Checking the number of pictures for skew partitions.
    # True for all n <= 5.
    for lam in SkewPartitions(n):
        Dlam = DiagramDoublePoset(lam, partition=True)
        for mu in SkewPartitions(n):
            Dmu = DiagramDoublePoset(mu, partition=True)
            Sym = SymmetricFunctions(QQ)
            s = Sym.s()
            if Dlam.number_of_pictures(Dmu) != s(lam).scalar(s(mu)):
                print(lam, mu)
                return False
    return True

