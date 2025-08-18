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

class LDPSym_abstract(CombinatorialFreeModule, BindableClass):
    r"""
    Abstract base class for bases of LDPSym
    (the combinatorial Hopf algebra of labelled
    double posets).

    This must define two attributes:

    - ``_prefix`` -- the basis prefix
    - ``_basis_name`` -- the name of the basis (must match one
      of the names that the basis can be constructed from `LDPSym`)
    """

    def __init__(self, alg, graded=True):

        def sorting_key(X):
            return (sorted(X.elements()),
                    sorted(X.poset(1).cover_relations()),
                    sorted(X.poset(2).cover_relations()))

        CombinatorialFreeModule.__init__(self, alg.base_ring(),
                                         DoublePosets(), #??????should it be this?
                                         category=LDPSymBases(alg, graded),
                                         sorting_key=sorting_key,
                                         bracket='', prefix=self._prefix)

    def _repr_term(self, dp):
        return self._prefix

    def _coerce_map_from_(self, R):
        r"""
        Return ``True`` if there is a coercion from ``R`` into ``self``
        and ``False`` otherwise.

        The things that coerce into ``self`` are

        - LDPSym over a base with
          a coercion map into ``self.base_ring()``

        EXAMPLES::

            sage: M = algebras.LDPSym(GF(7)).M(); M
            LDPSym over Finite Field of size 7 in the Monomial basis

        Elements of LDPSym canonically coerce in::

            sage: x, y = M([[1]]), M([[2,1]])
            sage: M.coerce(x+y) == x+y
            True

        LDPSym over `\ZZ` coerces in,
        since `\ZZ` coerces to `\GF{7}`::

            sage: N = algebras.LDPSym(ZZ).M()
            sage: Nx, Ny = N([[1]]), N([[2,1]])
            sage: z = M.coerce(Nx+Ny); z
            M[{1}] + M[{1, 2}]
            sage: z.parent() is M
            True

        However, `\GF{7}` does not coerce to `\ZZ`, so
        LDPSym over `\GF{7}` does not coerce
        to the same algebra over `\ZZ`::

            sage: N.coerce(y)
            Traceback (most recent call last):
            ...
            TypeError: no canonical coercion from LDPSym
             over Finite Field of size 7 in the Monomial basis to
             LDPSym over Integer Ring in the Monomial basis

        TESTS::

            sage: M = algebras.LDPSym(ZZ).M()
            sage: N = algebras.LDPSym(QQ).M()
            sage: M.has_coerce_map_from(N)
            False
            sage: N.has_coerce_map_from(M)
            True
            sage: M.has_coerce_map_from(QQ)
            False
            sage: N.has_coerce_map_from(QQ)
            True
            sage: M.has_coerce_map_from(PolynomialRing(ZZ, 3, 'x,y,z'))
            False
        """
        if isinstance(R, LDPSym_abstract):
            if R.realization_of() == self.realization_of():
                return True
            if not self.base_ring().has_coerce_map_from(R.base_ring()):
                return False
            if self._basis_name == R._basis_name:  # The same basis
                def coerce_base_ring(self, x):
                    return self._from_dict(x.monomial_coefficients())
                return coerce_base_ring
            # Otherwise lift that basis up and then coerce over
            target = getattr(self.realization_of(), R._basis_name)()
            return self._coerce_map_via([target], R)
        return super()._coerce_map_from_(R)

    def _an_element_(self):
        D = DoublePoset([(1,2)], [(1,3)], elements={1,2,3})
        E = DoublePoset([(1,2)], [(1,2), (1,3)], elements={1,2,3,4})
        return 2 * self(D) + 3 * self(E)

class LDPSym(UniqueRepresentation, Parent):
    r"""
    The combinatorial Hopf algebra `LDPSym`.

    This is a graded algebra, with a basis consisting of
    the double posets on ground sets `\{1,2,\ldots,n\}`
    for all `n \geq 0`.
    Multiplication is composition, while comultiplication
    is a sum over decompositions into order ideals/filters
    of the first order.
    For details, see [MalReu11]_, but keep in mind that
    our double posets are labelled, while those in
    [MalReu11]_ are isomorphism classes (so our Hopf
    algebra is larger).

    TODO: Doctests.
    """

    def __init__(self, R):
        """
        Initialize ``self``.

        TESTS::

            sage: A = algebras.LDPSym(QQ)
            sage: TestSuite(A).run()  # long time

            sage: M = algebras.LDPSym(ZZ).M()
            sage: M.is_commutative()
            False
        """
        category = HopfAlgebras(R).Graded().Connected()
        if R.is_zero():
            category = category.Commutative()
        Parent.__init__(self, base=R, category=category.WithRealizations())

    class Monomial(LDPSym_abstract):
        r"""
        The Monomial basis of `LDPSym`.

        This is just the family of the double posets
        (labelled, not taken up to isomorphism).

        EXAMPLES::

            sage: LDPSym = algebras.LDPSym(QQ)
            sage: M = LDPSym.M(); M
            LDPSym over Rational Field in the Monomial basis
            sage: sorted(LDP.basis(2))
            [M[{1}, {2}], M[{2}, {1}], M[{1, 2}]] # fix this
        """

        _prefix='M'
        _basis_name = 'Monomial'

        def product_on_basis(self, x, y):
            r"""
            Return the (associative) `*` product of the basis elements
            of ``self`` indexed by the double posets `x` and `y`.

            This is the composition of `x` and `y`.

            TODO: Doctests.
            """
            # K = self.basis().keys() # this is DoublePosets
            xy = x.compose(y, relabel=True).standardization()
            return self.monomial(xy)

        def coproduct_on_basis(self, x):
            r"""
            Return the coproduct of ``self`` on the basis element
            indexed by the double poset ``x``.

            TODO: Doctests.
            """
            T = self.tensor_square()
            return T.sum_of_monomials((y.standardization(), z.standardization())
                                      for (y, z) in x.decompositions_iter())

    M = Monomial

class LDPSymBases(Category_realization_of_parent):
    r"""
    The category of bases of `LDPSym`.
    """
    def __init__(self, base, graded):
        r"""
        Initialize ``self``.

        INPUT:

        - ``base`` -- an instance of `LDPSym`
        - ``graded`` -- boolean; if the basis is graded or filtered

        TESTS::

            sage: from sage.combinat.chas.ldpsym import LDPSymBases
            sage: LDPSym = algebras.LDPSym(ZZ)
            sage: bases = LDPSymBases(LDPSym, True)
            sage: LDPSym.M() in bases
            True
        """
        self._graded = graded
        Category_realization_of_parent.__init__(self, base)

    def _repr_(self):
        r"""
        Return the representation of ``self``.

        EXAMPLES::

            sage: from sage.combinat.chas.ldpsym import LDPSymBases
            sage: LDPSym = algebras.LDPSym(ZZ)
            sage: LDPSymBases(LDPSym, True)
            Category of graded bases of LDPSym over Integer Ring
            sage: LDPSymBases(LDPSym, False)
            Category of filtered bases of LDPSym over Integer Ring
        """
        if self._graded:
            type_str = "graded"
        else:
            type_str = "filtered"
        return "Category of {} bases of {}".format(type_str, self.base())

    def super_categories(self):
        r"""
        The super categories of ``self``.

        EXAMPLES::

            sage: from sage.combinat.chas.ldpsym import LDPSymBases
            sage: LDPSym = algebras.LDPSym(ZZ)
            sage: bases = LDPSymBases(LDPSym, True)
            sage: bases.super_categories()
            [Category of realizations of LDPSym over Integer Ring,
             Join of Category of realizations of Hopf algebras over Integer Ring
                 and Category of graded algebras over Integer Ring
                 and Category of graded coalgebras over Integer Ring,
             Category of graded connected Hopf algebras with basis over Integer Ring]

            sage: bases = LDPSymBases(LDPSym, False)
            sage: bases.super_categories()
            [Category of realizations of LDPSym over Integer Ring,
             Join of Category of realizations of Hopf algebras over Integer Ring
                 and Category of graded algebras over Integer Ring
                 and Category of graded coalgebras over Integer Ring,
             Join of Category of filtered connected Hopf algebras with basis over Integer Ring
                 and Category of graded algebras over Integer Ring
                 and Category of graded coalgebras over Integer Ring]
        """
        R = self.base().base_ring()
        cat = HopfAlgebras(R).Graded().WithBasis()
        if self._graded:
            cat = cat.Graded()
        else:
            cat = cat.Filtered()
        return [self.base().Realizations(),
                HopfAlgebras(R).Graded().Realizations(),
                cat.Connected()]

    class ParentMethods:
        def _repr_(self):
            """
            Text representation of this basis of `LDPSym`.

            EXAMPLES::

                sage: LDPSym = algebras.LDPSym(ZZ)
                sage: LDPSym.M()
                LDPSym over Integer Ring in the Monomial basis
            """
            return "{} in the {} basis".format(self.realization_of(), self._basis_name)

        def __getitem__(self, dp):
            """
            Return the basis element indexed by ``dp``.

            INPUT:

            - ``dp`` -- a double poset

            EXAMPLES::

                sage: M = algebras.LDPSym(QQ).M()
                sage: M[1, 2, 1]  # pass a word
                M[{1, 3}, {2}]
                sage: _ == M[[1, 2, 1]] == M[Word([1,2,1])]
                True
                sage: M[[1, 2, 3]]
                M[{1}, {2}, {3}]

                sage: M[[[1, 2, 3]]]  # pass an ordered set partition
                M[{1, 2, 3}]
                sage: _ == M[[1,2,3],] == M[OrderedSetPartition([[1,2,3]])]
                True
                sage: M[[1,3],[2]]
                M[{1, 3}, {2}]

            TESTS::

                sage: M[[]]
                M[]
                sage: M[1, 2, 1] == M[Word([2,3,2])] == M[Word('aca')]
                True
                sage: M[[[1,2]]] == M[1,1] == M[1/1,2/2] == M[2/1,2/1] == M['aa']
                True
                sage: M[1] == M[1,] == M[Word([1])] == M[OrderedSetPartition([[1]])] == M[[1],]
                True
            """
            try:
                return self.monomial(self._indices(p))
            except TypeError:
                raise ValueError("cannot convert %s into an element of %s" % (p, self._indices))

        def is_field(self, proof=True):
            """
            Return whether ``self`` is a field.

            EXAMPLES::

                sage: M = algebras.LDPSym(QQ).M()
                sage: M.is_field()
                False
            """
            return False

        def one_basis(self):
            """
            Return the index of the unit.

            EXAMPLES::

                sage: A = algebras.LDPSym(QQ).M()
                sage: A.one_basis()
                []
            """
            DP = self.basis().keys()
            return DP(Poset(), Poset())

        def degree_on_basis(self, dp):
            """
            Return the degree of a double poset in
            the algebra LDPSym.

            This is the size of the double poset.

            EXAMPLES::

                sage: A = algebras.LDPSym(QQ).M()
                sage: u = OrderedSetPartition([[2,1],])
                sage: A.degree_on_basis(u)
                2
                sage: u = OrderedSetPartition([[2], [1]])
                sage: A.degree_on_basis(u)
                2
            """
            return len(dp.elements())

    class ElementMethods:
        def flip(self):
            r"""
            Return the image of the element ``self`` of `LDPSym`
            under the flip involution.

            This means that all double posets in ``self`` get
            flipped.

            Note that this involution does not respect the
            algebra or coalgebra structures.

            TODO: Doctests.
            """
            # Convert to the Monomial basis, there apply the algebraic
            # complement componentwise, then convert back.
            parent = self.parent()
            M = parent.realization_of().M()
            dct = {I.flip(): coeff for I, coeff in M(self)}
            return parent(M._from_dict(dct, remove_zeros=False))

        def to_quasisymmetric_function(self):
            r"""
            The `\Gamma`-function of ``self`` in the ring `QSym` of
            quasisymmetric functions.

            OUTPUT: an element of the quasisymmetric functions in the monomial basis

            EXAMPLES::

                sage: M = algebras.LDPSym(QQ).M()
                sage: M[[1,3],[2]].to_quasisymmetric_function()
                M[2, 1]
                sage: (M[[1,3],[2]] + 3*M[[2,3],[1]] - M[[1,2,3],]).to_quasisymmetric_function()
                4*M[2, 1] - M[3]
                sage: X, Y = M[[1,3],[2]], M[[1,2,3],]
                sage: X.to_quasisymmetric_function() * Y.to_quasisymmetric_function() == (X*Y).to_quasisymmetric_function()
                True

                sage: C = algebras.LDPSym(QQ).C()
                sage: C[[2,3],[1,4]].to_quasisymmetric_function() == M(C[[2,3],[1,4]]).to_quasisymmetric_function()
                True

                sage: C2 = algebras.LDPSym(GF(2)).C()
                sage: C2[[1,2],[3,4]].to_quasisymmetric_function()
                M[2, 2]
                sage: C2[[2,3],[1,4]].to_quasisymmetric_function()
                M[4]
            """
            from sage.combinat.ncsf_qsym.qsym import QuasiSymmetricFunctions
            M = QuasiSymmetricFunctions(self.parent().base_ring()).Monomial()
            MW = self.parent().realization_of().M()
            return M.sum_of_terms((i.to_composition(), coeff)
                                  for i, coeff in MW(self))

        def to_fqsym(self):
            r"""
            The `L`-function of ``self`` in the ring `FQSym` of
            free quasisymmetric functions.

            This is more general than in [MalReu11]_:
            We are summing over all pairs of linear extensions
            of `<_1` and `<_2`.

            OUTPUT: an element of FQSym

            EXAMPLES::

                sage: M = algebras.LDPSym(QQ).M()
                sage: M[[1,3],[2]].to_quasisymmetric_function()
                M[2, 1]
                sage: (M[[1,3],[2]] + 3*M[[2,3],[1]] - M[[1,2,3],]).to_quasisymmetric_function()
                4*M[2, 1] - M[3]
                sage: X, Y = M[[1,3],[2]], M[[1,2,3],]
                sage: X.to_quasisymmetric_function() * Y.to_quasisymmetric_function() == (X*Y).to_quasisymmetric_function()
                True

                sage: C = algebras.LDPSym(QQ).C()
                sage: C[[2,3],[1,4]].to_quasisymmetric_function() == M(C[[2,3],[1,4]]).to_quasisymmetric_function()
                True

                sage: C2 = algebras.LDPSym(GF(2)).C()
                sage: C2[[1,2],[3,4]].to_quasisymmetric_function()
                M[2, 2]
                sage: C2[[2,3],[1,4]].to_quasisymmetric_function()
                M[4]
            """
            from sage.combinat.fqsym import FreeQuasisymmetricFunctions as FQSym
            F = FQSym(self.parent().base_ring()).F()
            MW = self.parent().realization_of().M()
            return F.sum_of_terms((i.to_composition(), coeff)
                                  for i, coeff in MW(self))

"""

# def Jollenbeck(sigma, tau):
#     from sage.combinat.permutation import Permutation
#     if not isinstance(sigma, Permutation):
#         sigma = Permutation(sigma)
#     if not isinstance(tau, Permutation):
#         sigma = Permutation(tau)

#     if sigma == tau.inverse(): return 1
#     return 0

