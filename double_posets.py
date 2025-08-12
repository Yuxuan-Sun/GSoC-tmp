# POSET FILE

#!/usr/bin/env python
# coding: utf-8

r"""
# Finite double posets

This class implements finite double posets, i.e., finite sets
equipped with two (unrelated) partial orders.

Notation used in the definitions follows mainly [MalReu95]_.

AUTHORS:

- Yuxuan Sun and Darij Grinberg (2025-08-07): first implementation

REFERENCES:

.. [MalReu95] \Claudia Malvenuto, Christophe Reutenauer, *A self paired Hopf algebra on double posets and a Littlewood–Richardson rule*, Journal of Combinatorial Theory, Series A
Volume 118, Issue 4, May 2011, pp. 1322--1333, https://doi.org/10.1016/j.jcta.2010.10.010 .

"""

# ****************************************************************************
#       Copyright (C) 2025 Yuxuan Sun <sun00816 at umn.edu>,
#                          Darij Grinberg <darijgrinberg at gmail.com>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 2 of
#  the License, or (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

from sage.structure.parent import Parent
from sage.structure.unique_representation import UniqueRepresentation
from sage.categories.finite_posets import FinitePosets
from sage.combinat.posets.posets import Poset
from itertools import permutations, product
from sage.rings.integer import Integer
from sage.rings.integer_ring import ZZ
from sage.rings.rational_field import QQ
from sage.categories.finite_enumerated_sets import FiniteEnumeratedSets
from sage.categories.infinite_enumerated_sets import InfiniteEnumeratedSets
from sage.combinat.posets.poset_examples import Posets
from sage.categories.sets_cat import Sets
from sage.sets.set import Set
from sage.structure.parent import Set_generic

class DoublePoset(Parent, UniqueRepresentation):
    r"""
    A (finite) double poset.

    This means a finite set `E` equipped with two
    partial orders `\leq_1` and `\leq_2`.
    See [MalReu95]_.

    INPUT:
    - ``P1`` -- either a list of covering relations or a Sage
                :class:`Poset` defining the first order `\leq_1`
    - ``P2`` -- likewise, defines the second order `\leq_2`
    - ``elements`` -- (optional) list/tuple/set of all elements
                      of the ground set;
                      by default, taken to be the ground set of ``P1``

    OUTPUT:

    ``DoublePoset`` -- an instance of the
    :class:`DoublePoset` class.

    If ``category`` is specified, then the poset is created in this
    category instead of :class:`DoublePosets`.

    EXAMPLES::

        sage: D = DoublePoset(Poset([[1,2,3,4],
        ....:                       [[1,2],[2,4],[1,3],[3,4]]]),
        ....:                       Poset([[1,2,3,4],[[2,3]]]))
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
        [[1, 2]]
        sage: D.poset(2).cover_relations()
        [[1, 3]]

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

        sage: D = DoublePoset([(1,2)], [(1,3)], elements={1,2,3})
        sage: D.elements()
        {1, 2, 3}
        sage: D = DoublePoset([(1,2)], [(1,3)], elements=(3,1,2,1))
        sage: D.elements()
        {1, 2, 3}

    Alternative ways to provide the arguments::

        sage: P = Poset([[1,2,3], [[1,2], [1,3]]])
        sage: Q = Poset([[1,2,3], [[1,2]]])
        sage: D = DoublePoset(P, Q)
        sage: E = DoublePoset(P, P2=Q)
        sage: F = DoublePoset([P, Q])
        sage: G = DoublePoset(D)
        sage: H = DoublePoset(P.cover_relations(),
        ....:                 Q.cover_relations(),
        ....:                 elements=[1,2,3])
        sage: D is E is F is G is H
        True

    """
    @staticmethod
    def __classcall__(cls, P1, P2=None, elements=None, category=None):
        """
        Normalize the arguments passed to the constructor.

        INPUT:

        - ``P1`` -- a finite poset `P_1`;
        - ``P2`` -- a finite poset `P_2`, required to equal
          `P_1` as a set
        """
        if P2 is None: # just one argument provided
            if isinstance(P1, DoublePoset):
                return P1
            return DoublePoset(P1[0], P1[1], elements=elements, category=category)
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

            sage: D = DoublePoset(Poset([[1,2,3,4],
            ....:                       [[1,2],[2,4],[1,3],[3,4]]]),
            ....:                       Poset([[1,2,3,4],[[2,3]]]))
            sage: TestSuite(D).run()

        See also the extensive tests in the class documentation.
        """
        Parent.__init__(self, category=category, facade=True)
        self._P1 = P1
        self._P2 = P2
        self._elements = tuple(P1)

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
        return set(self._elements)

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
        Return ``True`` if ``self`` is nonempty,
        ``False`` otherwise.

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

            sage: D = DoublePoset(Poset([[1,2],[[1,2]]]),
            ....:                 Poset([[1,2],[]]))
            sage: D.poset(1).relations()
            [[1, 1], [1, 2], [2, 2]]
            sage: D.poset(2).relations()
            [[2, 2], [1, 1]]
            sage: sorted(D.poset(2))
            [1, 2]
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

            sage: D = DoublePoset(Poset([[1,2],[[1,2]]]),
            ....:                 Poset([[1,2],[]]))
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
        Check if `a <_i b`, where `a` and `b` are two elements
        of ``self``, and `i` is either 1 or 2, referring to
        the `i`-th partial order.

        EXAMPLES::

            sage: D = DoublePoset(Poset([[1,2],[[1,2]]]),
            ....:                 Poset([[1,2],[]]))
            sage: D.is_less_than(1, 1, 2)
            True
            sage: D.is_less_than(1, 1, 1)
            False
            sage: D.is_less_than(2, 1, 2)
            False
            sage: D.is_less_than(2, 2, 2)
            False
        """
        return self.poset(i).is_less_than(a, b)

    lt = is_less_than

    def is_gequal(self, i, a, b):
        r"""
        Check if `a \geq_i b`, where `a` and `b` are two elements
        of ``self``, and `i` is either 1 or 2, referring to
        the `i`-th partial order.

        EXAMPLES::

            sage: D = DoublePoset(Poset([[1,2],[[1,2]]]),
            ....:                 Poset([[1,2],[]]))
            sage: D.is_gequal(1, 2, 1)
            True
            sage: D.is_gequal(1, 2, 2)
            True
            sage: D.is_gequal(2, 2, 1)
            False
            sage: D.is_gequal(2, 1, 1)
            True
        """
        return self.poset(i).is_gequal(a, b)

    geq = is_gequal

    def is_greater_than(self, i, a, b):
        r"""
        Check if `a >_i b`, where `a` and `b` are two elements
        of ``self``, and `i` is either 1 or 2, referring to
        the `i`-th partial order.

        EXAMPLES::

            sage: D = DoublePoset(Poset([[1,2],[[1,2]]]),
            ....:                 Poset([[1,2],[]]))
            sage: D.is_greater_than(1, 2, 1)
            True
            sage: D.is_greater_than(1, 1, 1)
            False
            sage: D.is_greater_than(2, 1, 2)
            False
        """
        return self.poset(i).is_greater_than(a, b)

    gt = is_greater_than

    def relabel(self, relabeling=None):
        r"""
        Relabel ``self`` using the relabeling
        function/dictionary ``relabeling``.

        The result is a double poset isomorphic to
        ``self``. Each element ``e`` of ``self`` is
        replaced by ``relabelling[e]``.

        See :meth:`FinitePoset.relabel` for the
        allowed syntax.

        EXAMPLES::

            sage: D = DoublePoset(Poset([[3,5,7], [[5,7], [7,3]]]),
            ....:                 Poset([[3,5,7], [[3,5]]]))
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

    def standardization(self, offset=1):
        r"""
        Relabel ``self`` so that the elements of
        ``self`` (in their Python order) become
        `1, 2, \ldots, n`.

        If the optional parameter ``offset`` is set
        to some integer `k`, then the elements are
        relabelled as `k, k+1, \ldots, k+n-1`
        instead.

        EXAMPLES::

            sage: D = DoublePoset(Poset([[3,5,7], [[5,7], [7,3]]]),
            ....:                 Poset([[3,5,7], [[3,5]]]))
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

        Standardization with an offset::

            sage: E = D.standardization(offset=5)
            sage: sorted(E.elements())
            [5, 6, 7]
            sage: E.poset(1).cover_relations()
            [[6, 7], [7, 5]]
            sage: E.poset(2).cover_relations()
            [[5, 6]]
        """
        els = sorted(self.elements())
        standardize = {elsi: i+offset for (i, elsi) in enumerate(els)}
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

        By default, this requires their ground sets
        to be disjoint.
        However, if the ``relabel`` parameter is set to
        ``True``, then each element `x` of ``self`` is
        relabelled as ``(1, x)`` whereas each element
        ``y`` of ``other`` is relabelled as ``(2, y)``;
        thus, the original ground sets need not be
        disjoint.

        Let ``self`` `= (E, <_1, <_2)` and
        ``other`` `= (F, <_1, <_2)`.
        The composition is a new double poset
        `EF = (E \cup F, <_1', <_2')` where:
        - `<_1'` is the disjoint union of the first
          orders of `E` and `F`;
        - `<_2'` is the ordinal sum: it contains all
          of the second orders of `E` and `F`, and
          for every `e \in E` and `f \in F`, we set
          `e <_2' f`.

        INPUT:

        - ``other`` -- another ``DoublePoset`` to
          compose with ``self``;
        - ``relabel`` (boolean, default: ``False``) --
          if ``True``, then each element `x` of
          ``self`` is relabelled as ``(1, x)`` whereas
          each element ``y`` of ``other`` is relabelled
          as ``(2, y)``.

        OUTPUT:

        - A new ``DoublePoset`` representing the
          composition of ``self`` and ``other``.

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

        TESTS::

            sage: D1 = DoublePoset(Poset([[1,2], [[1,2]]]), Poset([[1,2],[]]))
            sage: D2 = DoublePoset(Poset([[2,3], [[2,3]]]), Poset([[2,3],[]]))
            sage: D1.compose(D2)
            Traceback (most recent call last):
            ...
            ValueError: Double posets must be disjoint for doing composition

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
            raise ValueError("Double posets must be disjoint for doing composition")

        # First order: disjoint union
        rel1 = list(E1.cover_relations()) + list(F1.cover_relations())

        # Second order: ordinal sum
        rel2 = list(E2.cover_relations()) + list(F2.cover_relations()) \
               + [(e, f) for e in E2 for f in F2]

        return DoublePoset(rel1, rel2, elements=EF_elements)

    def decompositions_iter(self):
        r"""
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
                              elements=I)
            D_S = DoublePoset(P1_S.cover_relations(),
                              P2_S.cover_relations(),
                              elements=S)
            yield (D_I, D_S)

    def decompositions(self):
        r"""
        Return all decompositions of this double poset as
        pairs of double posets.

        A *decomposition* of a double poset
        `(E, <_1, <_2)` is a pair `(I, S)` such that:
          - `I` is an **inferior ideal** (order ideal)
            of the first order `<_1`;
          - `S = E \setminus I` is its complement;
          - both `I` and `S` inherit their orders
            `<_1` and `<_2` from `E`.

        This function returns all such decompositions,
        each as a pair of ``DoublePoset``s.

        OUTPUT:

        - A list of pairs `(I, S)` where `I` and `S`
          are ``DoublePoset`` instances.

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
            sage: for I, S in decs:
            ....:     print(sorted(I.poset(1).relations()), "|",
            ....:           sorted(I.poset(2).relations()))
            [] | []
            [[1, 1]] | [[1, 1]]
            [[1, 1], [1, 2], [2, 2]] | [[1, 1], [2, 2]]
            [[1, 1], [1, 3], [3, 3]] | [[1, 1], [1, 3], [3, 3]]
            [[1, 1], [1, 2], [1, 3], [2, 2], [3, 3]] | [[1, 1], [1, 3], [2, 2], [3, 3]]
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
            sage: D.flip().flip() is D
            True
            sage: D.flip() == D
            False
        """
        return DoublePoset(self._P2, self._P1)

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

        # get all bijections phi : E -> F
        for sigma in permutations(range(n)):
            phi = {Ei : F[sigma[i]] for (i, Ei) in enumerate(E)}
            phi_inv = {F[sigma[i]] : Ei for (i, Ei) in enumerate(E)}

            # Forward: e <_1 e′ => phi(e) <_2 phi(e′)
            forward_fail = any(
                D1.leq(1, e1, e2) and not D2.leq(2, phi[e1], phi[e2])
                for e1 in E for e2 in E if e1 != e2
            )

            if forward_fail:
                continue

            # Backward: f <_1 f′ => phi_inv(f) <_2 phi_inv(f′)
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

        A **picture** from a double poset
        `(E, \leq_1, \leq_2)` to a double poset
        `(F, \leq_1, \leq_2)` is a bijection
        `\phi: E \to F` such that:

        - if `e \leq_1 e'` in `E`, then
          `\phi(e) \leq_2 \phi(e')` in `F`;
        - if `f \leq_1 f'` in `F`, then
          `\phi^{-1}(f) \leq_2 \phi^{-1}(f')` in `E`.

        INPUT:

        - ``other`` -- a second ``DoublePoset``.

        OUTPUT:

        - A list of bijections (Python dicts)
          representing all valid pictures
          from ``self`` to ``other``.

        EXAMPLES::

            sage: E = DoublePoset([(1,2)], [(1,2)], elements=[1,2])
            sage: F = DoublePoset([(3,4)], [(3,4)], elements=[3,4])
            sage: E.pictures(F)
            [{1: 3, 2: 4}]
            sage: E.pictures(E)
            [{1: 1, 2: 2}]

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

        See :meth:`pictures`.

        EXAMPLES::

            sage: E = DoublePoset([(1,2)], [(1,2), (2,3)], elements=[1,2,3])
            sage: F = DoublePoset([(4,5), (5,6)], [(4,6)], elements=[4,5,6])
            sage: E.number_of_pictures(F)
            0
            sage: E = DoublePoset([(1,2)], [(1,2)], elements=[1,2])
            sage: F = DoublePoset([(3,4)], [(3,4)], elements=[3,4])
            sage: E.number_of_pictures(F)
            1
            sage: E = DoublePoset([(1,3), (2,3)], [(1,2), (2,3)], elements=[1,2,3])
            sage: F = DoublePoset([(4,6), (5,6)], [(4,5), (5,6)], elements=[4,5,6])
            sage: E.number_of_pictures(F)
            2
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

        # get all bijections phi : E -> F
        for sigma in permutations(range(n)):
            phi = {Ei : F[sigma[i]] for (i, Ei) in enumerate(E)}

            # Isomorphism of first orders
            order1_fail = any(
                D1.leq(1, e1, e2) != D2.leq(1, phi[e1], phi[e2])
                for e1 in E for e2 in E if e1 != e2
            )

            if order1_fail:
                continue

            # Isomorphism of second orders
            order2_fail = any(
                D1.leq(2, e1, e2) != D2.leq(2, phi[e1], phi[e2])
                for e1 in E for e2 in E if e1 != e2
            )

            if not order2_fail:
                yield phi

    def isomorphisms(self, other):
        r"""
        Return a list of all isomorphisms `\phi` from the double
        poset ``self`` to another double poset ``other``.
        The isomorphisms are encoded as dictionaries
        `\{e: \phi(e)\}`.

        An *isomorphism* between two double posets
        `(E, \leq_1, \leq_2)` and `(F, \leq_1, \leq_2)`
        is a bijection `\phi: E \to F` such that:

        - for all `e, e' \in E`,
          `\phi(e) \leq_1 \phi(e')` in `F`
          if and only if `e \leq_1 e'` in `E`;
        - for all `e, e' \in E`,
          `\phi(e) \leq_2 \phi(e')` in `F`
          if and only if `e \leq_2 e'` in `E`.

        INPUT:

        - ``other`` -- a second ``DoublePoset``.

        OUTPUT:

        - A list of bijections representing all
          isomorphisms from ``self`` to ``other``.

        EXAMPLES::

            sage: D1 = DoublePoset([(1,2)], [(1,2)], elements=[1,2])
            sage: D2 = DoublePoset([(3,4)], [(3,4)], elements=[3,4])
            sage: D1.isomorphisms(D2)
            [{1: 3, 2: 4}]
            sage: D1.isomorphisms(D1)
            [{1: 1, 2: 2}]

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

        See :meth:`isomorphisms`.

        EXAMPLES::

            sage: P1 = Poset(([1, 2], [[1, 2]]))
            sage: P2 = Poset(([1, 2], []))
            sage: Q1 = Poset(([3, 4], []))
            sage: Q2 = Poset(([3, 4], [[3, 4]]))
            sage: D1 = DoublePoset(P1, P2)
            sage: D2 = DoublePoset(Q1, Q2)
            sage: D1.number_of_isomorphisms(D2)
            0

            sage: B = posets.BooleanLattice(2)
            sage: D = DoublePoset(B, B)
            sage: D.number_of_isomorphisms(D)
            2

            sage: E = Poset(([1,2,3], []))
            sage: D1 = DoublePoset(E, E)
            sage: D1.number_of_isomorphisms(D1)
            6

            sage: P = Poset(([1,2,3], [[1,2],[2,3]]))
            sage: D2 = DoublePoset(P, P)
            sage: D2.number_of_isomorphisms(D2)
            1

            sage: D = DoublePoset(P, E)
            sage: D.number_of_isomorphisms(D)
            1

        """
        return sum(1 for _ in self.isomorphisms_iter(other))

    def is_isomorphic(self, other):
        r"""
        Return whether the double poset ``self`` is
        isomorphic to another double poset ``other``.

        See :meth:`isomorphisms`.

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

    def is_pi_partition(self, x):
        r"""
        Check if the given map ``x`` (provided as a
        dictionary with the elements of ``self`` as
        keys) is a `\pi`-partition of ``self``.

        Here, we do not require the output values of
        ``x`` to be positive integers; they merely
        have to belong to a totally ordered set.

        See :meth:`pi_partitions`.

        EXAMPLES::

            sage: D = DoublePoset([(1, 2), (1, 3)], [(2, 1)],
            ....:                 elements=[1, 2, 3])
            sage: D.is_pi_partition({1: 5, 2: 6, 3: 4})
            False
            sage: D.is_pi_partition({1: 2, 2: 2, 3: 4})
            False
            sage: D.is_pi_partition({1: 2, 2: 3, 3: 2})
            True
            sage: D.is_pi_partition({1: 0, 2: 0, 3: 0})
            False
        """
        E = list(self)
        for e1 in E:
            for e2 in E:
                if e1 == e2:
                    continue
                if self.leq(1, e1, e2):
                    if x[e1] > x[e2]:
                        return False
                    if self.geq(2, e1, e2) and x[e1] == x[e2]:
                        return False
        return True

    def pi_partitions_iter(self, bound):
        r"""
        Iterate over all `\pi`-partitions
        `x: E \to \{1, 2, ..., b\}` for this double poset,
        where `E` is the double poset ``self``, and
        where `b` is a nonnegative integer provided
        as the argument ``bound``.

        See :meth:`pi_partitions`.

        INPUT:

            - bound: positive integer ``b``; forces
              the values of ``x`` to be in ``{1,2,...,N}``
        """
        E = list(self)

        for values in product(range(1, bound+1), repeat=len(E)):
            x = dict(zip(E, values))
            if self.is_pi_partition(x):
                yield x

    def pi_partitions(self, bound):
        r"""
        Iterate over all `\pi`-partitions
        `x: E \to \{1, 2, ..., b\}` for this double poset,
        where `E` is the double poset ``self``, and
        where `b` is a nonnegative integer provided
        as the argument ``bound``.

        The `\pi`-partitions are encoded as dictionaries.

        A map `x: E \to \{1, 2, ..., b\}` is a
        `\pi`-partition if:
        - for any `e, e' \in E` satisfying `e <_1 e'`,
          we have `x(e) \leq x(e')`;
        - for any `e, e' \in E` satisfying `e <_1 e'`
          and `e \geq_2 e'`, we have `x(e) < x(e')`.

        INPUT:

            - bound: positive integer ``b``; forces
              the values of ``x`` to be in ``{1,2,...,b}``

        EXAMPLES::

            sage: D = DoublePoset([(1,2)], [(2,1)], elements=[1,2])
            sage: sorted([(x[1], x[2]) for x in D.pi_partitions(2)])
            [(1, 2)]

            sage: D = DoublePoset([(1,2)], [(2,1)], elements=[1,2])
            sage: sorted([(x[1], x[2]) for x in D.pi_partitions(3)])
            [(1, 2), (1, 3), (2, 3)]

            sage: D = DoublePoset([], [(1, 2)], elements=[1, 2])
            sage: sorted([(x[1], x[2]) for x in D.pi_partitions(2)])
            [(1, 1), (1, 2), (2, 1), (2, 2)]

            sage: D = DoublePoset([(1, 2), (2, 3)], [(1, 3)],
            ....:                 elements=[1, 2, 3])
            sage: len(D.pi_partitions(3))
            10
            sage: sorted([(x[1], x[2], x[3]) for x in D.pi_partitions(3)])
            [(1, 1, 1), (1, 1, 2), (1, 1, 3),
             (1, 2, 2), (1, 2, 3), (1, 3, 3),
             (2, 2, 2), (2, 2, 3), (2, 3, 3),
             (3, 3, 3)]

            sage: D = DoublePoset([(1,2), (2,3), (1,4)], [(1,3), (3,4)], elements=[1,2,3,4])
            sage: len(D.pi_partitions(4))
            65

        """
        return list(self.pi_partitions_iter(bound))

    def graph(self, other, phi):
        r"""
        Return the graph of two double posets
        ``self`` and ``other`` given a bijection ``phi``.

        If ``self`` is `E` and ``other`` is `F`, and
        if ``phi`` is a bijection `\phi : E \to F`, then
        this is `E \times_\phi F` as defined in
        [MalReu95]_. Explicitly, this is the set of all
        pairs `(e, \phi(e))`, equipped with the first
        order `<_1` inherited from `F` (that is, we let
        `(e, f) <_1 (e', f')` if and only if
        `f <_1 f'`) and the second order `<_2` inherited
        from `E` (that is, we let
        `(e, f) <_2 (e', f')` if and only if
        `e <_1 e'`).

        The bijection ``phi`` should be given as a
        dictionary `\{e: \phi(e)\}`.

        EXAMPLES::

            sage: E = DoublePoset([(1,2)], [(1,2)], elements=[1,2])
            sage: F = DoublePoset([(3,4)], [(3,4)], elements=[3,4])
            sage: G = E.graph(F, {1:3, 2:4})
            sage: G.elements()
            {(1, 3), (2, 4)}
            sage: G.poset(1).cover_relations()
            [[(1, 3), (2, 4)]]
            sage: G.poset(2).cover_relations()
            [[(1, 3), (2, 4)]]
            sage: G2 = E.graph(F, {1:4, 2:3})
            sage: G2.poset(1).cover_relations()
            [[(2, 3), (1, 4)]]
            sage: G2.poset(2).cover_relations()
            [[(1, 4), (2, 3)]]

            sage: D1 = DoublePoset([(1,2), (1,3), (2,4), (3,4)],
            ....:                  [(1,3), (2,3)], elements=[1,2,3,4])
            sage: D2 = DoublePoset([(5,6), (6,7), (7,8)],
            ....:                  [(5,7), (6,8)], elements=[5,6,7,8])
            sage: phi = {1:6, 2:5, 3:8, 4:7}
            sage: G = D1.graph(D2, phi)
            sage: G.elements()
            {(1, 6), (2, 5), (3, 8), (4, 7)}
            sage: G.poset(1).cover_relations()
            [[(2, 5), (1, 6)], [(1, 6), (4, 7)], [(4, 7), (3, 8)]]
            sage: G.poset(2).cover_relations()
            [[(2, 5), (3, 8)], [(1, 6), (3, 8)]]
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
                    cov1.append(((e1,f1), (e2,f2)))

        # second order: (e, f) <_2 (e', f') iff e <_2 e' in D1
        for (e1, f1) in elements:
            for (e2, f2) in elements:
                if e1 != e2 and D1.leq(2, e1, e2):
                    cov2.append(((e1,f1), (e2,f2)))

        D_phi = DoublePoset(cov1, cov2, elements=elements)

        return D_phi

class SpecialDoublePoset(DoublePoset):
    r"""
    A special double poset is a double poset `(E, \leq_1, \leq_2)` 
    where the second order `\leq_2` is a total order.

    EXAMPLES::

        sage: from sage.combinat.posets.double_posets import SpecialDoublePoset
        sage: P1 = Poset(([1, 2, 3], [(1,2)]))
        sage: P2 = Poset(([1, 2, 3], [(1,2), (2,3)]))  # total order
        sage: SD = SpecialDoublePoset(P1, P2)
        sage: SD
        Special double poset containing 3 elements
        sage: SD.poset(2).is_chain()
        True

        sage: from sage.combinat.posets.double_posets import SpecialDoublePoset
        sage: P2 = Poset(([1, 2, 3], [(1,2)]))  # not total
        sage: SpecialDoublePoset(P1, P2)
        Traceback (most recent call last):
        ...
        ValueError: The second order must be a total order.
    """
    @staticmethod
    def __classcall__(cls, P1, P2, elements=None, category=None):
        
        D = super(SpecialDoublePoset, cls).__classcall__(cls, P1, P2, elements=elements, category=category)

        
        if not D._P2.is_chain():
            raise ValueError("The second order must be a total order.")
        return D

    def _repr_(self):
        return "Special double poset containing " + str(len(self)) + " elements"





def internal_product_helper(D1, D2):
    r"""
    Iterate over all graphs ``D1`` `\times_phi` ``D2``
    for all increasing bijections ``phi`` from ``D1``
    to ``D2``.

    The internal product in the Hopf algebra
    is the sum of these graphs.

    TODO::

        Doctest this.
    """

    E = D1.elements()
    F = D2.elements()

    if len(E) != len(F):
        return

    n = len(E)

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
    [MalReu95]_, but serves the same purpose
    (encoding James-Peel/Zelevinsky pictures
    between skew Young diagrams).

    The diagram `D` can be provided as an
    iterable consisting of pairs `(i, j)`, or,
    if a skew Young diagram is desired, as a
    skew partition (:class:`SkewPartition`).
    In the latter case, the optional parameter
    ``partition`` must be set to ``True``.

    EXAMPLES::

        sage: from sage.combinat.posets.double_posets import DiagramDoublePoset
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

        sage: from sage.combinat.posets.double_posets import DiagramDoublePoset
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
        from sage.combinat.skew_partition import SkewPartition
        cells = SkewPartition(D).cells()
    else:
        cells = list(set(D))
    rel1 = [(c, d) for c in cells for d in cells
            if c[0] <= d[0] and c[1] <= d[1]]
    rel2 = [(c, d) for c in cells for d in cells
            if c[0] <= d[0] and c[1] >= d[1]]
    return DoublePoset(rel1, rel2, elements=cells)

def check_LR(n):
    # To be removed from the final version.
    # Checking the number of pictures for skew partitions.
    # True for all n <= 5.
    from sage.combinat.skew_partition import SkewPartitions
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

class DoublePosets(UniqueRepresentation, Parent):
    """
    Return the combinatorial class of double posets on
    a given ground set ``s``.

    EXAMPLES::

        sage: DPs = DoublePosets([1,2,3]); DPs
        Double posets with ground set {1, 2, 3}
        sage: DPs.cardinality()
        25
        sage: DPs.first()
        [{1}, {2}, {3}, {4}]
        sage: DPs.last()
        [{1, 2, 3, 4}]
        sage: DPs.random_element().parent() is OS
        True

    ::

        sage: DPs = DoublePosets("cat")
        sage: DPs  # random
        Double posets of {'a', 't', 'c'}
        sage: DPs.first()
        [[{'a', 'c', 't'}],
         [{'a', 'c'}, {'t'}],
         [{'a', 't'}, {'c'}],
         [{'a'}, {'c', 't'}],
         [{'a'}, {'c'}, {'t'}],
         [{'a'}, {'t'}, {'c'}],
         [{'c', 't'}, {'a'}],
         [{'c'}, {'a', 't'}],
         [{'c'}, {'a'}, {'t'}],
         [{'c'}, {'t'}, {'a'}],
         [{'t'}, {'a', 'c'}],
         [{'t'}, {'a'}, {'c'}],
         [{'t'}, {'c'}, {'a'}]]

    TESTS::

        sage: S = DoublePosets()
        sage: x = S([[3,5], [2], [1,4,6]])
        sage: x.parent()
        Ordered set partitions
    """
    @staticmethod
    def __classcall_private__(cls, s=None):
        """
        Choose the correct parent based upon input.

        EXAMPLES::

            sage: DoublePosets(4)
            Double posets on {1, 2, 3, 4}
            sage: DoublePosets(4, [1, 2, 1])
            Double posets on {1, 2, 3, 4} into parts of size [1, 2, 1]
        """
        if s is None:
            return DoublePosets_all()
        if isinstance(s, (int, Integer)):
            if s < 0:
                raise ValueError("s must be nonnegative")
            s = frozenset(range(1, s + 1))
        else:
            s = frozenset(s)

        return DoublePosets_s(s)

    def __init__(self, s):
        """
        Initialize ``self``.

        EXAMPLES::

            sage: OS = DoublePosets(4)
            sage: TestSuite(OS).run()
        """
        self._set = s
        Parent.__init__(self, category=FiniteEnumeratedSets())

    def _element_constructor_(self, s):
        """
        Construct an element of ``self`` from ``s``.

        EXAMPLES::

            sage: OS = DoublePosets(4)
            sage: x = OS([[1,3],[2,4]]); x
            [{1, 3}, {2, 4}]
            sage: x.parent()
            Double posets on {1, 2, 3, 4}
        """
        return self.element_class(self, s)

    Element = DoublePoset

    def __contains__(self, x):
        """
        TESTS::

            sage: OS = DoublePosets([1,2,3,4])
            sage: all(sp in OS for sp in OS)
            True
            sage: [[1,2], [], [3,4]] in OS
            False
            sage: [Set([1,2]), Set([3,4])] in OS
            True
            sage: [set([1,2]), set([3,4])] in OS
            True

        Make sure the set really matches::

            sage: [set([5,6]), set([3,4])] in OS
            False
        """
        return isinstance(x, DoublePoset)

class DoublePosets_all(DoublePosets):
    r"""
    Double posets on ground sets `\{1, \ldots, n\}` for all
    `n \in \ZZ_{\geq 0}`.
    """

    def __init__(self):
        """
        Initialize ``self``.

        EXAMPLES::

            sage: OS = DoublePosets()
            sage: TestSuite(OS).run()  # long time
        """
        Parent.__init__(self, category=InfiniteEnumeratedSets())

    def subset(self, size=None, **kwargs):
        """
        Return the subset of double posets of a given
        size and additional keyword arguments.

        EXAMPLES::

            sage: P = DoublePosets()
            sage: P.subset(4)
            Double posets on {1, 2, 3, 4}
        """
        if size is None:
            return self
        return DoublePosets(size, **kwargs)

    def __iter__(self):
        """
        Iterate over ``self``.

        EXAMPLES::

            sage: it = iter(DoublePosets())
            sage: [next(it) for _ in range(10)]
            [[], [{1}], [{1}, {2}], [{2}, {1}], [{1, 2}],
             [{1}, {2}, {3}], [{1}, {3}, {2}], [{2}, {1}, {3}],
             [{3}, {1}, {2}], [{2}, {3}, {1}]]
        """
        n = 0
        while True:
            for X in DoublePosets(n):
                yield self.element_class(X)
            n += 1

    def _element_constructor_(self, s):
        """
        Construct an element of ``self`` from ``s``.

        EXAMPLES::

            sage: OS = DoublePosets()
            sage: OS([[1,3],[2,4]])
            [{1, 3}, {2, 4}]
        """
        if isinstance(s, DoublePoset):
            gset = set(s.elements())
            if gset == frozenset(range(1, len(gset) + 1)):
                return self.element_class(self, list(s))
            raise ValueError("cannot convert %s into an element of %s" % (s, self))
        return self.element_class(s)

    def __contains__(self, x):
        """
        TESTS::

            sage: OS = DoublePosets([1,2,3,4])
            sage: AOS = DoublePosets()
            sage: all(sp in AOS for sp in OS)
            True
            sage: AOS.__contains__([[1,3], [4], [5,2]])
            True
            sage: AOS.__contains__([Set([1,3]), Set([4]), Set([5,2])])
            True
            sage: [Set([1,4]), Set([3])] in AOS
            False
            sage: [Set([1,3]), Set([4,2]), Set([2,5])] in AOS
            False
            sage: [Set([1,2]), Set()] in AOS
            False
        """
        if not isinstance(x, DoublePoset):
            return False

        elts = tuple(sorted(x.elements()))
        n = len(elts)
        return elts == tuple(range(1, n+1))

    def _coerce_map_from_(self, X):
        """
        Return ``True`` if there is a coercion map from ``X``.

        EXAMPLES::

            sage: OSP = DoublePosets()
            sage: OSP._coerce_map_from_(DoublePosets(3))
            True
            sage: OSP._coerce_map_from_(DoublePosets(['a','b']))
            False
        """
        if X is self:
            return True
        if isinstance(X, DoublePosets):
            elts = X.elements()
            n = len(elts)
            return frozenset(elts) == frozenset(range(1, n + 1))
        return super()._coerce_map_from_(X)

    def _repr_(self):
        """
        TESTS::

            sage: DoublePosets()
            Double posets
        """
        return "Double posets"

    class Element(DoublePoset):
        pass


class DoublePosets_s(DoublePosets):
    """
    Class of double posets on a given ground set `S`.
    """

    def _repr_(self):
        """
        TESTS::

            sage: DoublePosets([1,2,3,4])
            Double posets on {1, 2, 3, 4}
        """
        return "Double posets on %s" % Set(self._set)

    def cardinality(self):
        """
        EXAMPLES::

            sage: DoublePosets(0).cardinality()
            1
            sage: DoublePosets(1).cardinality()
            1
            sage: DoublePosets(2).cardinality()
            3
            sage: DoublePosets(3).cardinality()
            13
            sage: DoublePosets([1,2,3]).cardinality()
            13
            sage: DoublePosets(4).cardinality()
            75
            sage: DoublePosets(5).cardinality()
            541
        """
        return Posets(len(self._set)).cardinality() ** 2

    def __iter__(self):
        """
        EXAMPLES::

            sage: list(DoublePosets([1,2,3]))
            [[{1}, {2}, {3}],
             [{1}, {3}, {2}],
             [{2}, {1}, {3}],
             [{3}, {1}, {2}],
             [{2}, {3}, {1}],
             [{3}, {2}, {1}],
             [{1}, {2, 3}],
             [{2}, {1, 3}],
             [{3}, {1, 2}],
             [{1, 2}, {3}],
             [{1, 3}, {2}],
             [{2, 3}, {1}],
             [{1, 2, 3}]]

        TESTS:

        Test for :issue:`35654`::

            sage: DoublePosets(set(),[0,0,0]).list()
            [[{}, {}, {}]]
        """
        n = len(self._set)
        Slist = sorted(list(self._set))
        relabeling_dict = {i: Si for (i, Si) in enumerate(Slist)}
        for P1 in Posets(n):
            P1 = P1.relabel(relabeling_dict)
            for P2 in Posets(n):
                P2 = P2.relabel(relabeling_dict)
                yield self.element_class(DoublePoset(P1, P2))

    def __contains__(self, x):
        """
        TESTS::

            sage: OS = DoublePosets([1,2,3,4])
            sage: AOS = DoublePosets()
            sage: all(sp in AOS for sp in OS)
            True
            sage: AOS.__contains__([[1,3], [4], [5,2]])
            True
            sage: AOS.__contains__([Set([1,3]), Set([4]), Set([5,2])])
            True
            sage: [Set([1,4]), Set([3])] in AOS
            False
            sage: [Set([1,3]), Set([4,2]), Set([2,5])] in AOS
            False
            sage: [Set([1,2]), Set()] in AOS
            False
        """
        if not isinstance(x, DoublePoset):
            return False

        elts = frozenset(x.elements())
        return elts == frozenset(self._set)

    class Element(DoublePoset):
        pass


# HOPF ALGEBRA FILE:


# sage.doctest: needs sage.combinat sage.modules
r"""
Labelled double poset Hopf algebra (LDPSym)

AUTHORS:

- Yuxuan Sun and Darij Grinberg (2025-08-07): first implementation

TESTS:

TODO
"""

# ****************************************************************************
#       Copyright (C) 2025 Yuxuan Sun <sun00816 at umn.edu>,
#                          Darij Grinberg <darijgrinberg at gmail.com>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 2 of
#  the License, or (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

from sage.misc.bindable_class import BindableClass
from sage.structure.parent import Parent
from sage.structure.unique_representation import UniqueRepresentation
from sage.structure.global_options import GlobalOptions
from sage.categories.hopf_algebras import HopfAlgebras
from sage.categories.realizations import Category_realization_of_parent
from sage.combinat.free_module import CombinatorialFreeModule
from sage.rings.integer_ring import ZZ
# TODO: from sage.combinat.posets.double_posets import DoublePoset, DoublePosets


class LabelledDoublePosetsHA(UniqueRepresentation, Parent):

    def __init__(self, R):
        """
        Initialize ``self``.

        """
        category = HopfAlgebras(R).Graded().Connected()
        if R.is_zero():
            category = category.Commutative()
        Parent.__init__(self, base=R, category=category.WithRealizations())


def Jollenbeck(sigma, tau):
    from sage.combinat.permutation import Permutation
    if not isinstance(sigma, Permutation):
        sigma = Permutation(sigma)
    if not isinstance(tau, Permutation):
        sigma = Permutation(tau)

    if sigma == tau.inverse(): return 1
    return 0
