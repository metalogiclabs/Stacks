module

public import StacksFrontier.AlgebraicGeometry.Spaces.LocalRingDimensionIso
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointSmoothChart
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionAtPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothPresentationLocalRingDimension
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting

/-!
# Chart independence for the dimension of the local ring of an algebraic stack (Stacks 0DS9)

**Stacks 0DS9** states, for a locally Noetherian algebraic stack `𝒳`, a finite type point
`x ∈ |𝒳|` and an integer `d`, the equivalence of

1. there *exists* a scheme `U`, a smooth morphism `U ⟶ 𝒳` and a finite type point `u ∈ U` over
   `x` with `2 dim(𝒪_{U,ū}) - dim(𝒪_{R,e(ū)}) = d`, and
2. *every* such `U`, smooth morphism and finite type point `u` over `x` satisfies that identity.

Condition (1) is `AlgebraicGeometry.Stack.HasLocalRingDimensionAtSomeChart`, and condition (2)
is `AlgebraicGeometry.Stack.HasLocalRingDimensionAtEveryChart`; this file defines both and proves
the implication from (2) to (1).

## Main definitions

* `AlgebraicGeometry.Stack.HasLocalRingDimensionAtSomeChart`: **condition (1) of Stacks 0DS9**,
  the relation of Stacks 0DSA, with the chart read through its canonical comparison equivalence.
* `AlgebraicGeometry.Stack.HasLocalRingDimensionAtEveryChart`: **condition (2) of Stacks 0DS9**,
  the universally quantified form of condition (1).

## Main results

* `AlgebraicGeometry.Stack.exists_hasLocalRingDimensionAtSomeChart`: condition (1) holds for some
  integer at a point carrying a smooth chart with a finite type point above it.
* `AlgebraicGeometry.Stack.exists_smoothChart_presentation_of_isFiniteTypePoint`: a finite type
  point of a locally Noetherian algebraic stack carries at least one of the configurations that
  the two conditions quantify over.
* `AlgebraicGeometry.Stack.hasLocalRingDimensionAtSomeChart_of_hasLocalRingDimensionAtEveryChart`:
  **Stacks 0DS9, condition (2) implies condition (1)**.
* `AlgebraicGeometry.Stack.hasRelationLocalRingDimension_transport_equivalence`: the invariant of
  Stacks 0DSA does not depend on the comparison equivalences presenting the chart and the
  relation, nor on the mediating morphism giving the diagonal — once the point it is read at is
  transported along the comparison automorphism of the chart.
* `AlgebraicGeometry.Stack.forall_hasRelationLocalRingDimension_transport_equivalence`: the same
  independence with the point universally quantified, so that no transport of the point is
  visible. Neither of these is what makes the conditions of Stacks 0DS9 well posed — those fix
  the equivalence presenting the chart to the canonical one; they are the comparison a consumer
  needs when a *construction* delivers the relation presented at an equivalence other than the
  one it wants.

## Implementation notes

Condition (2) is written with *exactly* the binders and side conditions of condition (1), the
sole change being `∃` for `∀` and the side conditions becoming hypotheses: the scheme `V` of the
site, the 1-morphism `g`, the 2-fibre product square `T` for the cospan `(g, g)` together with
its terminality, the algebraic space `Q` presenting its apex with its presenting equivalence, the
mediating morphism `δ` giving the diagonal, and the point `ν` of the chart. This matters: the two
conditions of the source quantify over the same data, so reading (2) over a *smaller* range of
configurations than (1) ranges over would make the implication proved here vacuous, and reading
it over a larger one would make it a different statement.

**Neither condition quantifies over the equivalence presenting the chart, and neither may.** Both
read the invariant through the canonical identification of `V` with the presheaf it represents,
`CategoryTheory.PresheafOfCategories.sliceElementsEquivalenceOver`, which is the identification
their side conditions on `ν` are already stated through —
`AlgebraicGeometry.Stack.representedChartPointMap` is defined at it. Quantifying over it as well
makes hypothesis and conclusion speak about two different identifications of `|V|`, and both
conditions then say something other than the source's:

* an `∃` in condition (1) leaves `d` undetermined, so Stacks 0DSA fails to define anything. The
  counterexample is recorded below, under "The counterexample to the quantified form".
* an `∀` in condition (2) demands the invariant at *every* point of the orbit of `ν` under the
  automorphisms of `V`, over points of `|𝒳|` other than `x`. The same counterexample refutes
  `(1) ⇒ (2)` in that form.

**The counterexample to the quantified form.** The relation
`AlgebraicGeometry.Stack.HasLocalRingDimension` reads the invariant through an existentially
quantified comparison equivalence `eV`, and in that form it is satisfied by two different
integers at one point:

> Take `S = Spec k`, `𝒳 = 𝐀¹ ⊔ pt` (a scheme, hence an algebraic stack),
> `V = 𝐀¹ ⊔ 𝐀¹` and `g : V ⟶ 𝒳` the disjoint union of the isomorphism onto the `𝐀¹` component
> and of the structure morphism `𝐀¹ ⟶ pt`, which is smooth. Let `ν` be the origin of the second
> component and `x = pt` its image. The relation over the second component is
> `𝐀¹ ×_{pt} 𝐀¹ = 𝐀²` and the diagonal carries `ν` to its origin, so the invariant at `ν` is
> `2·1 - 2 = 0`. Now `V` has the automorphism `α` swapping its two components, and `α` is an
> automorphism over `S`. Composing the canonical equivalence with the equivalence of categories
> of elements that `yoneda.map α` induces is again an equivalence over the site — that is all
> `StacksRepresentableCFG.EquivalenceOver` asks — and reading the invariant through it at `ν`
> gives the invariant read canonically at `α(ν)`, by
> `AlgebraicGeometry.Stack.hasRelationLocalRingDimension_transport_equivalence` together with
> `AlgebraicGeometry.Stack.representingIso_trans_equivalenceOverOfIso`. Over the first component
> `g` is an isomorphism, so the relation there is `𝐀¹` with the diagonal an isomorphism, and that
> invariant is `2·1 - 1 = 1`. The two side conditions are conditions on `ν` and are untouched, so
> the quantified form of condition (1) holds at `x` both for `d = 0` and for `d = 1`.

The definitions of this file therefore fix the identification to
`CategoryTheory.PresheafOfCategories.sliceElementsEquivalenceOver`, the one the side conditions
already use, and agree with how Stacks 0DS9 itself states the two conditions.

Both follow from one fact, that the comparison isomorphism of two presentations of a category
fibred in groupoids takes *every* value an isomorphism of presheaves can take
(`AlgebraicGeometry.Stack.representingIso_trans_equivalenceOverOfIso`): a presentation is an
equivalence over the site and nothing more, so one may be composed with the equivalence of
categories of elements induced by any automorphism of `yoneda.obj V`, which by Yoneda is
`yoneda.map` of an automorphism of `V`.

**The remaining comparison data does drop out, and that is a theorem rather than a convention.**
The 2-fibre product square `T`, the presenting algebraic space `Q`, its equivalence `eQ` and the
mediating morphism `δ` are quantified over, and the invariant does not depend on them:
`AlgebraicGeometry.Stack.hasRelationLocalRingDimension_transport_twoFibreProduct`, which needs no
transport of the point of the chart, since the comparison of two presented self-intersections is
an isomorphism of the two representing presheaves of the *relation*.

**For an equivalence presenting the chart, the independence is a compatible transport, not an
invariance at a fixed point** — which is why it cannot be used to absorb a quantifier over that
equivalence in a predicate whose side conditions are canonical. Changing it replaces the
morphism of representing presheaves of Stacks 04SW by its conjugate
(`AlgebraicGeometry.Stack.representingMap_congr_equivalenceOver`), and the conjugating
automorphism of `yoneda.obj V` moves the points of the chart. So the statement that holds is the
one in which the point is carried along that automorphism; asserting the invariant at one and the
same point of `V` for two presentations would be false. Along the transport the two comparison
automorphisms cancel against each other — neither is trivial on its own.

The implication from (2) to (1) is then purely a matter of exhibiting one configuration, which is
`AlgebraicGeometry.Stack.exists_smoothChart_presentation_of_isFiniteTypePoint`: the chart comes
from the implication of **Stacks 06FX** that a finite type point of an algebraic stack is the
image of a closed point of a scheme smooth over it, and a closed point of a scheme is a finite
type point of it because the morphism from the spectrum of its residue field is then a closed
immersion. The 2-fibre product square and its terminality are the standard construction, the
apex of a 2-fibre product of two schemes over an algebraic stack is representable by an algebraic
space because the diagonal of `𝒳` is, and the mediating morphism is supplied by terminality.

Local Noetherianity of `𝒳` and finite-typeness of `x` are arguments of the predicate but are used
in neither body: they are what gives the defining conditions their content.

## References

* [Stacks Project, Tag 06FX](https://stacks.math.columbia.edu/tag/06FX)
* [Stacks Project, Tag 0DS9](https://stacks.math.columbia.edu/tag/0DS9)
* [Stacks Project, Tag 0DSA](https://stacks.math.columbia.edu/tag/0DSA)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Condition (1) of Stacks 0DS9, the relation of Stacks 0DSA.** There is a scheme `V` of the
site with a smooth 1-morphism `g : V ⟶ 𝒳`, a presented self-intersection `R = V ×_𝒳 V` with
diagonal `e`, and a finite type point `ν` of `V` lying over `x`, such that
`2 dim(𝒪_{V,ν̄}) - dim(𝒪_{R, e(ν̄)}) = d`.

The identification of `V` with the presheaf it represents is the canonical one,
`CategoryTheory.PresheafOfCategories.sliceElementsEquivalenceOver`, which is the identification
the two side conditions on `ν` already use. This is
`AlgebraicGeometry.Stack.HasLocalRingDimension` with that identification fixed instead of
existentially quantified; the quantified form does not determine `d`, by the counterexample in
the module documentation. -/
@[stacks 0DSA]
def HasLocalRingDimensionAtSomeChart (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (_h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (x : points B S hS 𝒳.val.val 𝒳.val.property)
    (_hx : IsFiniteTypePoint.{u, w} B S hS 𝒳 x) (d : ℤ) : Prop :=
  ∃ (V : BigFppfOver B S hS) (g : schemeStack.{u, w} B S hS V ⟶ 𝒳)
      (T : Bicategory.TwoCommSq g g) (_hT : Bicategory.IsTwoFibreProduct T)
      (Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hQ : IsAlgebraicSpace B S hS Q)
      (eQ : StacksRepresentableCFG.EquivalenceOver
        T.pt.val.val.p (presheafOfCategories (Q ⋙ typeToCat)).p)
      (δ : Bicategory.TwoCommSq.PreHom (selfIntersectionDiagonalSquare B S hS V g) T)
      (ν : Space.points B S hS (yoneda.obj V)),
    AlgebraicStacks.IsSmooth B S hS g ∧
      AlgebraicGeometry.IsFiniteTypePoint (Space.pointsToScheme B S hS V ν) ∧
        pointsMap B S hS (schemeFibredCategory B S hS V).val
            (schemeFibredCategory B S hS V).property 𝒳.val.property g.hom.hom
            (representedChartPointMap B S hS V ν) = x ∧
          HasRelationLocalRingDimension B S hS V g T Q
            (PresheafOfCategories.sliceElementsEquivalenceOver V) eQ
            (Space.pointsMap B S hS (yoneda.obj V)
              (selfIntersectionDiagonalMap B S hS V g T Q
                (PresheafOfCategories.sliceElementsEquivalenceOver V) eQ δ) ν) d

/-- **Condition (1) of Stacks 0DS9 is satisfied by some integer** as soon as the point has a
smooth chart with a finite type point above it: both local rings entering the invariant are
Noetherian local rings, so Krull's height theorem makes the two dimensions finite. The witness
is built at the canonical comparison equivalence of the chart. -/
theorem exists_hasLocalRingDimensionAtSomeChart {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (U : BigFppfOver B S hS) (f : schemeStack.{u, w} B S hS U ⟶ 𝒳)
    (sq : Bicategory.TwoCommSq f f) (R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eR : StacksRepresentableCFG.EquivalenceOver
      sq.pt.val.val.p (presheafOfCategories (R ⋙ typeToCat)).p)
    (hf : AlgebraicStacks.IsSmooth B S hS f)
    (hsq : Bicategory.IsTwoFibreProduct sq)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳) (hR : IsAlgebraicSpace B S hS R)
    (δ : Bicategory.TwoCommSq.PreHom (selfIntersectionDiagonalSquare B S hS U f) sq)
    (ν : Space.points B S hS (yoneda.obj U))
    (hν : AlgebraicGeometry.IsFiniteTypePoint (Space.pointsToScheme B S hS U ν))
    (x : points B S hS 𝒳.val.val 𝒳.val.property)
    (hx : IsFiniteTypePoint.{u, w} B S hS 𝒳 x)
    (hνx : pointsMap B S hS (schemeFibredCategory B S hS U).val
      (schemeFibredCategory B S hS U).property 𝒳.val.property f.hom.hom
      (representedChartPointMap B S hS U ν) = x) :
    ∃ d : ℤ, HasLocalRingDimensionAtSomeChart B S hS 𝒳 h𝒳 x hx d := by
  obtain ⟨r, hr⟩ := Space.exists_geometricRepresentative B S hS R
    (Space.pointsMap B S hS (yoneda.obj U)
      (selfIntersectionDiagonalMap B S hS U f sq R
        (PresheafOfCategories.sliceElementsEquivalenceOver U) eR δ) ν)
  obtain ⟨d, hd⟩ := exists_hasChartLocalRingDimension B S hS U f sq R
    (PresheafOfCategories.sliceElementsEquivalenceOver U) eR hf hsq h𝒳 hR r
  exact ⟨d, U, f, sq, hsq, R, hR, eR, δ, ν, hf, hν, hνx,
    hr ▸ (hasChartLocalRingDimension_iff_hasRelationLocalRingDimension
      B S hS U f sq R (PresheafOfCategories.sliceElementsEquivalenceOver U) eR hR r d).1 hd⟩

/-- **Condition (2) of Stacks 0DS9.** For *every* scheme `V` of the site carrying a smooth
1-morphism `g : V ⟶ 𝒳`, every presented self-intersection `R = V ×_𝒳 V` with diagonal `e`, and
every finite type point `ν` of `V` lying over `x`, the invariant
`2 dim(𝒪_{V,ν̄}) - dim(𝒪_{R, e(ν̄)})` equals `d`.

The binders are exactly those of `AlgebraicGeometry.Stack.HasLocalRingDimensionAtSomeChart`,
which is condition (1); only the quantifier differs.

**The comparison equivalence of the chart is the canonical one, and must not be quantified
over**, exactly as in condition (1) and for the mirror-image reason: an `∀` over it would demand
the invariant at every point of the orbit of `ν` under the automorphisms of `V`, hence over
points of `|𝒳|` other than `x`, while the two side conditions stay conditions on `ν`. The
implementation notes give the argument and the counterexample. -/
def HasLocalRingDimensionAtEveryChart (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (_h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (x : points B S hS 𝒳.val.val 𝒳.val.property)
    (_hx : IsFiniteTypePoint.{u, w} B S hS 𝒳 x) (d : ℤ) : Prop :=
  ∀ (V : BigFppfOver B S hS) (g : schemeStack.{u, w} B S hS V ⟶ 𝒳)
      (T : Bicategory.TwoCommSq g g) (_hT : Bicategory.IsTwoFibreProduct T)
      (Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hQ : IsAlgebraicSpace B S hS Q)
      (eQ : StacksRepresentableCFG.EquivalenceOver
        T.pt.val.val.p (presheafOfCategories (Q ⋙ typeToCat)).p)
      (δ : Bicategory.TwoCommSq.PreHom (selfIntersectionDiagonalSquare B S hS V g) T)
      (ν : Space.points B S hS (yoneda.obj V)),
    AlgebraicStacks.IsSmooth B S hS g →
      AlgebraicGeometry.IsFiniteTypePoint (Space.pointsToScheme B S hS V ν) →
        pointsMap B S hS (schemeFibredCategory B S hS V).val
            (schemeFibredCategory B S hS V).property 𝒳.val.property g.hom.hom
            (representedChartPointMap B S hS V ν) = x →
          HasRelationLocalRingDimension B S hS V g T Q
            (PresheafOfCategories.sliceElementsEquivalenceOver V) eQ
            (Space.pointsMap B S hS (yoneda.obj V)
              (selfIntersectionDiagonalMap B S hS V g T Q
                (PresheafOfCategories.sliceElementsEquivalenceOver V) eQ δ) ν) d

/-- A closed point of a scheme is a finite type point of it: the morphism from the spectrum of
its residue field is then a closed immersion, hence locally of finite type and quasi-compact. -/
theorem isFiniteTypePoint_of_isClosed {X : Scheme.{u}} {t : X}
    (ht : IsClosed ({t} : Set X)) : AlgebraicGeometry.IsFiniteTypePoint t :=
  have : AlgebraicGeometry.IsClosedImmersion (X.fromSpecResidueField t) :=
    AlgebraicGeometry.isClosed_singleton_iff_isClosedImmersion.mp ht
  ⟨inferInstance, inferInstance⟩

/-! ### The invariant at a point of the relation: existence and uniqueness -/

/-- **The invariant read off a point of the relation determines the integer.** Both dimensions
entering it are functions of that point alone, so their difference is too.

This is the companion of `AlgebraicGeometry.Stack.hasChartLocalRingDimension_unique` for
`AlgebraicGeometry.Stack.HasRelationLocalRingDimension`, and it is what lets the invariant's
value be compared between two configurations: the chart comparison of Stacks 0DS9 yields
equalities of integers, and without uniqueness those would not pin down a single `d`. -/
theorem hasRelationLocalRingDimension_unique {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (U : BigFppfOver B S hS) (f : schemeStack.{u, w} B S hS U ⟶ 𝒳)
    (sq : Bicategory.TwoCommSq f f) (R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eU : StacksRepresentableCFG.EquivalenceOver
      (schemeStack.{u, w} B S hS U).val.val.p
      (presheafOfCategories (yoneda.obj U ⋙ typeToCat)).p)
    (eR : StacksRepresentableCFG.EquivalenceOver
      sq.pt.val.val.p (presheafOfCategories (R ⋙ typeToCat)).p)
    (ρ : Space.points B S hS R) {d e : ℤ}
    (hd : HasRelationLocalRingDimension B S hS U f sq R eU eR ρ d)
    (he : HasRelationLocalRingDimension B S hS U f sq R eU eR ρ e) : d = e := by
  obtain ⟨m, n, hm, hn, hd'⟩ := hd
  obtain ⟨m', n', hm', hn', he'⟩ := he
  have hmm : m = m' := by exact_mod_cast hm.symm.trans hm'
  have hnn : n = n' := by exact_mod_cast hn.symm.trans hn'
  omega

/-- **The invariant is realized by an integer at every point of the relation** of a presented
self-intersection of a smooth chart of a locally Noetherian algebraic stack.

Pick a geometric point above the given point — one exists — and apply
`AlgebraicGeometry.Stack.exists_hasChartLocalRingDimension`, which is finiteness of the two
dimensions; the invariant depends only on the point of the relation by
`AlgebraicGeometry.Stack.hasChartLocalRingDimension_iff_hasRelationLocalRingDimension`. Together
with `AlgebraicGeometry.Stack.hasRelationLocalRingDimension_unique` this makes the invariant a
well-defined integer at each configuration, which is what the chart comparison of Stacks 0DS9
compares. -/
theorem exists_hasRelationLocalRingDimension {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (U : BigFppfOver B S hS) (f : schemeStack.{u, w} B S hS U ⟶ 𝒳)
    (sq : Bicategory.TwoCommSq f f) (R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eU : StacksRepresentableCFG.EquivalenceOver
      (schemeStack.{u, w} B S hS U).val.val.p
      (presheafOfCategories (yoneda.obj U ⋙ typeToCat)).p)
    (eR : StacksRepresentableCFG.EquivalenceOver
      sq.pt.val.val.p (presheafOfCategories (R ⋙ typeToCat)).p)
    (hf : AlgebraicStacks.IsSmooth B S hS f) (hsq : Bicategory.IsTwoFibreProduct sq)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳) (hR : IsAlgebraicSpace B S hS R)
    (ρ : Space.points B S hS R) :
    ∃ d : ℤ, HasRelationLocalRingDimension B S hS U f sq R eU eR ρ d := by
  obtain ⟨r, hr⟩ := Space.exists_geometricRepresentative B S hS R ρ
  obtain ⟨d, hd⟩ := exists_hasChartLocalRingDimension B S hS U f sq R eU eR hf hsq h𝒳 hR r
  exact ⟨d, hr ▸ (hasChartLocalRingDimension_iff_hasRelationLocalRingDimension
    B S hS U f sq R eU eR hR r d).1 hd⟩

/-! ### The self-intersection of a refined chart, by pasting -/

/-- **The self-intersection of a refined chart, as a pasted rectangle.** Let `f : U ⟶ 𝒳` be a
chart, `sq` a 2-fibre product square for `(f, f)` — so its apex is `R = U ×_𝒳 U` — and
`h : U' ⟶ U` a refinement of the chart by a morphism of the site. Given a 2-fibre product square
`Q` for `(h, t)`, whose apex is `U' ×_{h,U,t} R`, and one `T` for `(pr ≫ s, h)`, whose apex is
`(U' ×_{h,U,t} R) ×_{s,U} U'`, the rectangle obtained by pasting first along the *first*
projection and then along the second is a 2-commutative square over the cospan `(g', g')` of the
refined chart `g' = h ≫ f`.

The nesting is chosen to match the doubled base change `(U' ×_{h,U,t} R) ×_{s,U} U'` used for the
chart comparison, so that no associativity comparison of iterated fibre products is needed when
this is pushed down to representing presheaves. Pasting in the other order gives the
canonically isomorphic `U' ×_{h,U} (R ×_{s,U} U')` and would require one.

That this rectangle really *is* a 2-fibre product is
`AlgebraicGeometry.Stack.isTwoFibreProduct_refinedSelfIntersectionSquare`. -/
noncomputable abbrev refinedSelfIntersectionSquare {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {U U' : BigFppfOver B S hS} {f : schemeStack.{u, w} B S hS U ⟶ 𝒳} {h : U' ⟶ U}
    (sq : Bicategory.TwoCommSq f f)
    (Q : Bicategory.TwoCommSq (schemeStackMap.{u, w} B S hS h) sq.fst)
    (T : Bicategory.TwoCommSq (sq.pasteFst Q).snd (schemeStackMap.{u, w} B S hS h)) :
    Bicategory.TwoCommSq (schemeStackMap.{u, w} B S hS h ≫ f)
      (schemeStackMap.{u, w} B S hS h ≫ f) :=
  (sq.pasteFst Q).paste T

/-- **The pasted rectangle is a 2-fibre product**, so the self-intersection of a refined chart
`U' ⟶ U ⟶ 𝒳` is the triple product `U' ×_U (U ×_𝒳 U) ×_U U'`, that is,
`U' ×_𝒳 U' = (U' ×_U U) ×_𝒳 U = (U' ×_{h,U,t} R) ×_{s,U} U'`. -/
noncomputable def isTwoFibreProduct_refinedSelfIntersectionSquare
    {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {U U' : BigFppfOver B S hS} {f : schemeStack.{u, w} B S hS U ⟶ 𝒳} {h : U' ⟶ U}
    {sq : Bicategory.TwoCommSq f f} (hsq : Bicategory.IsTwoFibreProduct sq)
    (Q : Bicategory.TwoCommSq (schemeStackMap.{u, w} B S hS h) sq.fst)
    (hQ : Bicategory.IsTwoFibreProduct Q)
    {T : Bicategory.TwoCommSq (sq.pasteFst Q).snd (schemeStackMap.{u, w} B S hS h)}
    (hT : Bicategory.IsTwoFibreProduct T) :
    Bicategory.IsTwoFibreProduct (refinedSelfIntersectionSquare B S hS sq Q T) :=
  Bicategory.isTwoFibreProduct_paste
    (Bicategory.isTwoFibreProduct_pasteFst sq hsq Q hQ) hT

/-- **The `ℤ`-valued invariant of Stacks 0DSA is determined by the subtraction-free identity.**
Suppose the four `ringKrullDim`s entering the invariant at two charts are the natural numbers
`m, n` and `m', n'`, and that they satisfy the subtraction-free form
`2 dim(𝒪_{U',ū'}) + dim(𝒪_{R,e(ū)}) = 2 dim(𝒪_{U,ū}) + dim(𝒪_{R',e(ū')})`
of the chart comparison of Stacks 0DS9. Then the two integers `2m' - n'` and `2m - n` agree.

This is the step that turns an identity in `WithBot ℕ∞`, which has no subtraction fit to express
the invariant, into an equality of integers: the four dimensions are named as natural numbers
first — legitimate because each ring is a Noetherian local ring, so Krull's height theorem bounds
its dimension, which is `AlgebraicGeometry.Stack.exists_hasChartLocalRingDimension` — and the
subtraction is then taken in `ℤ`, where it is total. No cancellation in `WithBot ℕ∞` is performed
or needed.

**The pairing is crossed in the hypothesis and straight in the conclusion, and that is correct.**
The intended binding is `a' = dim(𝒪_{U',ū'})`, `b = dim(𝒪_{R,e(ū)})`, `a = dim(𝒪_{U,ū})`,
`b' = dim(𝒪_{R',e(ū')})`, so the hypothesis pairs the primed chart with the *unprimed* relation
while the conclusion pairs each chart with *its own* relation:
`2 dim(𝒪_{U',ū'}) - dim(𝒪_{R',e(ū')}) = 2 dim(𝒪_{U,ū}) - dim(𝒪_{R,e(ū)})`. The crossing is
exactly what clearing the two differences produces, and reversing it would silently compute an
invariant pairing each chart with the *other* chart's relation — which is not the invariant of
Stacks 0DSA. -/
theorem two_mul_sub_eq_two_mul_sub_of_add_add_eq {a b a' b' : WithBot ℕ∞} {m n m' n' : ℕ}
    (ha : a = (m : WithBot ℕ∞)) (hb : b = (n : WithBot ℕ∞))
    (ha' : a' = (m' : WithBot ℕ∞)) (hb' : b' = (n' : WithBot ℕ∞))
    (h : a' + a' + b = a + a + b') :
    2 * (m' : ℤ) - (n' : ℤ) = 2 * (m : ℤ) - (n : ℤ) := by
  rw [ha, hb, ha', hb'] at h
  have hnat : m' + m' + n = m + m + n' := by exact_mod_cast h
  omega

/-- **Shrinking a chart to one in which the point is closed.** A finite type point `ν` of a
scheme `V` of the site is a closed point of an affine open `W ⊆ V`, and the inclusion of `W`
carries the corresponding point of `W` back to `ν`.

This is the first reduction of the proof of Stacks 0DS9 — "we may shrink `U` and `U'` so that
the points become closed" — in the form in which the chart quantifier of the tag's two
conditions needs it: the tag quantifies over FINITE TYPE points, and this is what produces a
closed one without strengthening that quantifier. The scheme-theoretic content is
**Stacks 02J2**, that the finite type points of a scheme are exactly the points closed in some
affine open. -/
theorem exists_affChart_isClosed_of_isFiniteTypePoint (V : BigFppfOver B S hS)
    (ν : Space.points B S hS (yoneda.obj V))
    (hν : AlgebraicGeometry.IsFiniteTypePoint (Space.pointsToScheme B S hS V ν)) :
    ∃ (i : ((BigFppfOver.toScheme B S hS).obj V).affineOpens)
      (ω : Space.points B S hS (yoneda.obj (affChart V i))),
      IsClosed ({Space.pointsToScheme B S hS (affChart V i) ω} :
        Set ((BigFppfOver.toScheme B S hS).obj (affChart V i))) ∧
        Space.pointsMap B S hS (yoneda.obj (affChart V i))
          (yoneda.map (affChartHom V i)) ω = ν := by
  have hmem : Space.pointsToScheme B S hS V ν ∈
      ((BigFppfOver.toScheme B S hS).obj V).finiteTypePoints := hν
  rw [Scheme.finiteTypePoints_eq_iUnion_affineOpens] at hmem
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
  obtain ⟨t, htc, hteq⟩ := hi
  obtain ⟨ω, hω⟩ := Space.surjective_pointsToScheme B S hS (affChart V i) t
  refine ⟨i, ω, ?_, ?_⟩
  · rw [hω]
    exact mem_closedPoints_iff.mp htc
  · refine Space.injective_pointsToScheme B S hS V ?_
    rw [Space.pointsToScheme_pointsMap, hω, affChartHom_toScheme]
    exact hteq

/-- **Every smooth chart of an algebraic stack admits a presented self-intersection.** For a
1-morphism `g : V ⟶ 𝒳` from the algebraic stack of a scheme of the site there are a 2-fibre
product square `T` for the cospan `(g, g)` and an algebraic space `Q` presenting its apex: the
2-fibre product is the standard construction, and its apex is representable by an algebraic space
because the diagonal of an algebraic stack is (**Stacks 04SV**).

The mediating morphism `δ` giving the diagonal `e : V ⟶ R` needs no separate existence statement:
terminality of `T` supplies one through
`CategoryTheory.Bicategory.twoFibreProductPreHom`. -/
theorem exists_presentedSelfIntersection {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (V : BigFppfOver B S hS) (g : schemeStack.{u, w} B S hS V ⟶ 𝒳) :
    ∃ (T : Bicategory.TwoCommSq g g) (_hT : Bicategory.IsTwoFibreProduct T)
      (Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hQ : IsAlgebraicSpace B S hS Q),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        T.pt.val.val.p (presheafOfCategories (Q ⋙ typeToCat)).p) := by
  have hgrep : IsRepresentableByAlgebraicSpaces B S hS g.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒳.property
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS V) g.hom
  obtain ⟨Q, hQ, heQ⟩ : IsRepresentableByAlgebraicSpace B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS g g).pt.val :=
    isRepresentableByAlgebraicSpace_twoFibreProduct B S hS 𝒳.val
      (schemeStack.{u, w} B S hS V).val (schemeStack.{u, w} B S hS V).val
      g.hom.hom g.hom.hom hgrep
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS V)
  exact ⟨twoFibreProductSquareAlgebraicStacks B S hS g g,
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g g, Q, hQ, heQ⟩

/-- **A finite type point of an algebraic stack carries at least one of the configurations that
the two conditions of Stacks 0DS9 quantify over**: a scheme `V` of the site, a smooth 1-morphism
`g : V ⟶ 𝒳`, a 2-fibre product square for the cospan `(g, g)` whose apex is presented by an
algebraic space, the mediating morphism giving the diagonal, and a finite type point of `V`
above `x`.

The chart and its point come from **Stacks 06FX**, which supplies a *closed* point of a scheme
smooth over `𝒳` above `x`; a closed point is in particular a finite type point. The apex of the
2-fibre product is representable by an algebraic space because the diagonal of an algebraic stack
is, and the mediating morphism is supplied by terminality of a 2-fibre product.

The chart is presented by the canonical equivalence, which is the one the two conditions of
Stacks 0DS9 read the invariant through; it is not quantified over here for the same reason it is
not quantified over there. -/
theorem exists_smoothChart_presentation_of_isFiniteTypePoint
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (x : points B S hS 𝒳.val.val 𝒳.val.property)
    (hx : IsFiniteTypePoint.{u, w} B S hS 𝒳 x) :
    ∃ (V : BigFppfOver B S hS) (g : schemeStack.{u, w} B S hS V ⟶ 𝒳)
      (T : Bicategory.TwoCommSq g g) (_hT : Bicategory.IsTwoFibreProduct T)
      (Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hQ : IsAlgebraicSpace B S hS Q)
      (_eQ : StacksRepresentableCFG.EquivalenceOver
        T.pt.val.val.p (presheafOfCategories (Q ⋙ typeToCat)).p)
      (_δ : Bicategory.TwoCommSq.PreHom (selfIntersectionDiagonalSquare B S hS V g) T)
      (ν : Space.points B S hS (yoneda.obj V)),
      AlgebraicStacks.IsSmooth B S hS g ∧
        AlgebraicGeometry.IsFiniteTypePoint (Space.pointsToScheme B S hS V ν) ∧
          pointsMap B S hS (schemeFibredCategory B S hS V).val
            (schemeFibredCategory B S hS V).property 𝒳.val.property g.hom.hom
            (representedChartPointMap B S hS V ν) = x := by
  obtain ⟨V, g, z, hgsm, hzcl, hzx⟩ :=
    exists_isClosed_smoothChart_of_isFiniteTypePoint.{u, w} B S hS 𝒳 x hx
  obtain ⟨T, hT, Q, hQ, ⟨eQ⟩⟩ := exists_presentedSelfIntersection B S hS V g
  obtain ⟨ν, hν⟩ := (bijective_representedChartPointMap B S hS V).surjective z
  refine ⟨V, g, T, hT, Q, hQ, eQ,
    Bicategory.twoFibreProductPreHom hT (selfIntersectionDiagonalSquare B S hS V g),
    ν, hgsm, ?_, ?_⟩
  · refine isFiniteTypePoint_of_isClosed ?_
    rw [← pointsHomeomorphScheme_representedChartPointMap B S hS V ν, hν]
    exact hzcl
  · rw [hν]; exact hzx

/-- **Stacks 0DS9, condition (2) implies condition (1).** If every smooth chart of a locally
Noetherian algebraic stack `𝒳` carrying a finite type point above `x` measures the invariant of
Stacks 0DSA to be `d`, then some one does — because, by **Stacks 06FX**, there is one.

This direction of the equivalence is exactly the non-emptiness of the range of the two
quantifiers, supplied by
`AlgebraicGeometry.Stack.exists_smoothChart_presentation_of_isFiniteTypePoint`. -/
@[stacks 0DS9 "condition (2) implies condition (1)"]
theorem hasLocalRingDimensionAtSomeChart_of_hasLocalRingDimensionAtEveryChart
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (x : points B S hS 𝒳.val.val 𝒳.val.property)
    (hx : IsFiniteTypePoint.{u, w} B S hS 𝒳 x) (d : ℤ)
    (h : HasLocalRingDimensionAtEveryChart.{u, w} B S hS 𝒳 h𝒳 x hx d) :
    HasLocalRingDimensionAtSomeChart.{u, w} B S hS 𝒳 h𝒳 x hx d := by
  obtain ⟨V, g, T, hT, Q, hQ, eQ, δ, ν, hgsm, hνft, hνx⟩ :=
    exists_smoothChart_presentation_of_isFiniteTypePoint.{u, w} B S hS 𝒳 x hx
  exact ⟨V, g, T, hT, Q, hQ, eQ, δ, ν, hgsm, hνft, hνx,
    h V g T hT Q hQ eQ δ ν hgsm hνft hνx⟩

/-! ### Independence of the comparison equivalences and of the mediating morphism -/

section Transport

variable {𝒳 : AlgebraicStacks.{u, w} B S hS} (V : BigFppfOver B S hS)
  (g : schemeStack.{u, w} B S hS V ⟶ 𝒳) (T : Bicategory.TwoCommSq g g)
  (Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (eV eV' : StacksRepresentableCFG.EquivalenceOver
    (schemeStack.{u, w} B S hS V).val.val.p
    (presheafOfCategories (yoneda.obj V ⋙ typeToCat)).p)
  (eQ eQ' : StacksRepresentableCFG.EquivalenceOver
    T.pt.val.val.p (presheafOfCategories (Q ⋙ typeToCat)).p)

/-- **Changing the comparison equivalences conjugates the source morphism** `s : R ⟶ V` of a
presented self-intersection: read off the primed equivalences it is the morphism read off the
unprimed ones, precomposed with the comparison automorphism of the relation and postcomposed with
that of the chart.

This is `AlgebraicGeometry.Stack.representingMap_congr_equivalenceOver` at the second leg of the
square. **The two equivalences enter the source morphism in the opposite order to the one they
are listed in**: `AlgebraicGeometry.Stack.selfIntersectionSourceMap` takes `(eV, eQ)` and feeds
`AlgebraicGeometry.Stack.representingMap` the pair `(eQ, eV)`, since the source presheaf is `Q`
and the target is `yoneda.obj V`. Both slots can typecheck in some instantiations, so the
conjugating isomorphisms are named with their categories fibred in groupoids spelled out. -/
theorem selfIntersectionSourceMap_congr_equivalenceOver :
    selfIntersectionSourceMap B S hS V g T Q eV' eQ' =
      (representingIso (𝒲 := T.pt.val) B S hS Q Q eQ eQ').inv ≫
        selfIntersectionSourceMap B S hS V g T Q eV eQ ≫
          (representingIso (𝒲 := (schemeStack.{u, w} B S hS V).val) B S hS
            (yoneda.obj V) (yoneda.obj V) eV eV').hom :=
  representingMap_congr_equivalenceOver (𝒜 := T.pt.val)
    (𝒞 := (schemeStack.{u, w} B S hS V).val) B S hS Q Q (yoneda.obj V) (yoneda.obj V)
    eQ eQ' eV eV' T.snd.hom

/-- **Changing the comparison equivalences conjugates the diagonal** `e : V ⟶ R` of a presented
self-intersection, the conjugation running the other way than for the source morphism because the
diagonal goes from the chart to the relation.

Again `AlgebraicGeometry.Stack.representingMap_congr_equivalenceOver`, now at the 1-morphism
underlying the mediating morphism `δ`. -/
theorem selfIntersectionDiagonalMap_congr_equivalenceOver
    (δ : Bicategory.TwoCommSq.PreHom (selfIntersectionDiagonalSquare B S hS V g) T) :
    selfIntersectionDiagonalMap B S hS V g T Q eV' eQ' δ =
      (representingIso (𝒲 := (schemeStack.{u, w} B S hS V).val) B S hS
          (yoneda.obj V) (yoneda.obj V) eV eV').inv ≫
        selfIntersectionDiagonalMap B S hS V g T Q eV eQ δ ≫
          (representingIso (𝒲 := T.pt.val) B S hS Q Q eQ eQ').hom :=
  representingMap_congr_equivalenceOver (𝒜 := (schemeStack.{u, w} B S hS V).val)
    (𝒞 := T.pt.val) B S hS (yoneda.obj V) (yoneda.obj V) Q Q eV eV' eQ eQ' δ.hom.hom

/-- **The diagonal does not depend on the mediating morphism.** Any two morphisms of
2-commutative squares from the tautological square into a 2-fibre product are 2-cell equivalent
by terminality (`CategoryTheory.Bicategory.twoFibreProductPreHom_rel`), and the identification of
Stacks 04SW is constant on 2-isomorphism classes
(`AlgebraicGeometry.Stack.representingMap_congr_twoIso`), so they induce the same morphism of
representing presheaves. -/
theorem selfIntersectionDiagonalMap_congr_preHom (hT : Bicategory.IsTwoFibreProduct T)
    (δ δ' : Bicategory.TwoCommSq.PreHom (selfIntersectionDiagonalSquare B S hS V g) T) :
    selfIntersectionDiagonalMap B S hS V g T Q eV eQ δ =
      selfIntersectionDiagonalMap B S hS V g T Q eV eQ δ' := by
  obtain ⟨θ, -, -⟩ := Bicategory.twoFibreProductPreHom_rel hT δ δ'
  exact representingMap_congr_twoIso (𝒜 := (schemeStack.{u, w} B S hS V).val)
    (𝒞 := T.pt.val) B S hS (yoneda.obj V) Q eV eQ
    (Bicategory.InducedBicategory.isoHom (f := δ.hom) (g := δ'.hom) θ)

/-- **The invariant of Stacks 0DSA does not depend on the comparison data of a presented
self-intersection.** Let a smooth chart `g : V ⟶ 𝒳` and a 2-fibre product square `T` for the
cospan `(g, g)` be presented in two ways — by equivalences `eV, eQ` with a mediating morphism `δ`
and by `eV', eQ'` with `δ'` — and let `ν` be a point of the chart. Then the invariant measured by
the first presentation at the diagonal image of `ν` is `d` exactly when the invariant measured by
the second is `d` at the diagonal image of the point `ν` *transported along the comparison
automorphism of the chart*.

This is the chart-independence input of condition (2) of **Stacks 0DS9**, which quantifies over
arbitrary comparison equivalences while condition (1) supplies only some. The predicate depends on
the comparison data solely through `AlgebraicGeometry.Stack.selfIntersectionSourceMap`, but the
point it is read at is itself the diagonal image, so both the morphism and the point move: the
statement is a compatible transport, not an invariance at a fixed point, and the transport is what
makes the two comparison automorphisms cancel. Neither of them is trivial on its own — the
comparison automorphism of the chart is a nontrivial automorphism of `yoneda.obj V` in general.

Concretely, the diagonal image on the right is the image under the comparison automorphism of the
*relation* of the diagonal image on the left, and the source morphism on the right is the
conjugate of the one on the left; the automorphism of the relation therefore cancels when the
source morphism is applied, leaving only the automorphism of the chart, and that one is an
isomorphism of presheaves, under which the dimension of the local ring of **Stacks 04NA** is
unchanged (`AlgebraicGeometry.Space.localRingDimension_pointsMap_iso_hom`, which needs no
algebraicity hypothesis: the two sets of chart values realized are literally equal).

Independence of the mediating morphism is absorbed here rather than stated apart, since
terminality of `T` makes any two of them 2-cell equivalent; that is the one place terminality is
used, and `AlgebraicGeometry.Stack.selfIntersectionDiagonalMap_congr_preHom` isolates it. -/
theorem hasRelationLocalRingDimension_transport_equivalence
    (hT : Bicategory.IsTwoFibreProduct T)
    (δ δ' : Bicategory.TwoCommSq.PreHom (selfIntersectionDiagonalSquare B S hS V g) T)
    (ν : Space.points B S hS (yoneda.obj V)) (d : ℤ) :
    HasRelationLocalRingDimension B S hS V g T Q eV eQ
        (Space.pointsMap B S hS (yoneda.obj V)
          (selfIntersectionDiagonalMap B S hS V g T Q eV eQ δ) ν) d ↔
      HasRelationLocalRingDimension B S hS V g T Q eV' eQ'
        (Space.pointsMap B S hS (yoneda.obj V)
          (selfIntersectionDiagonalMap B S hS V g T Q eV' eQ' δ')
          (Space.pointsMap B S hS (yoneda.obj V)
            (representingIso (𝒲 := (schemeStack.{u, w} B S hS V).val) B S hS
              (yoneda.obj V) (yoneda.obj V) eV eV').hom ν)) d := by
  have hdiag : (representingIso (𝒲 := (schemeStack.{u, w} B S hS V).val) B S hS
          (yoneda.obj V) (yoneda.obj V) eV eV').hom ≫
        selfIntersectionDiagonalMap B S hS V g T Q eV' eQ' δ' =
      selfIntersectionDiagonalMap B S hS V g T Q eV eQ δ ≫
        (representingIso (𝒲 := T.pt.val) B S hS Q Q eQ eQ').hom := by
    rw [selfIntersectionDiagonalMap_congr_equivalenceOver B S hS V g T Q eV eV' eQ eQ' δ',
      selfIntersectionDiagonalMap_congr_preHom B S hS V g T Q eV eQ hT δ' δ,
      ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hsource : (representingIso (𝒲 := T.pt.val) B S hS Q Q eQ eQ').hom ≫
        selfIntersectionSourceMap B S hS V g T Q eV' eQ' =
      selfIntersectionSourceMap B S hS V g T Q eV eQ ≫
        (representingIso (𝒲 := (schemeStack.{u, w} B S hS V).val) B S hS
          (yoneda.obj V) (yoneda.obj V) eV eV').hom := by
    rw [selfIntersectionSourceMap_congr_equivalenceOver B S hS V g T Q eV eV' eQ eQ',
      ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hpt : Space.pointsMap B S hS (yoneda.obj V)
        (selfIntersectionDiagonalMap B S hS V g T Q eV' eQ' δ')
        (Space.pointsMap B S hS (yoneda.obj V)
          (representingIso (𝒲 := (schemeStack.{u, w} B S hS V).val) B S hS
            (yoneda.obj V) (yoneda.obj V) eV eV').hom ν) =
      Space.pointsMap B S hS Q (representingIso (𝒲 := T.pt.val) B S hS Q Q eQ eQ').hom
        (Space.pointsMap B S hS (yoneda.obj V)
          (selfIntersectionDiagonalMap B S hS V g T Q eV eQ δ) ν) :=
    by rw [← Space.pointsMap_comp_apply, ← Space.pointsMap_comp_apply, hdiag]
  have hdim : Space.localRingDimension B S hS
        (Space.pointsMap B S hS (yoneda.obj V)
          (selfIntersectionDiagonalMap B S hS V g T Q eV' eQ' δ')
          (Space.pointsMap B S hS (yoneda.obj V)
            (representingIso (𝒲 := (schemeStack.{u, w} B S hS V).val) B S hS
              (yoneda.obj V) (yoneda.obj V) eV eV').hom ν)) =
      Space.localRingDimension B S hS
        (Space.pointsMap B S hS (yoneda.obj V)
          (selfIntersectionDiagonalMap B S hS V g T Q eV eQ δ) ν) := by
    rw [hpt]
    exact Space.localRingDimension_pointsMap_iso_hom B S hS
      (representingIso (𝒲 := T.pt.val) B S hS Q Q eQ eQ') _
  have hsdim : Space.localRingDimension B S hS
        (Space.pointsMap B S hS Q (selfIntersectionSourceMap B S hS V g T Q eV' eQ')
          (Space.pointsMap B S hS (yoneda.obj V)
            (selfIntersectionDiagonalMap B S hS V g T Q eV' eQ' δ')
            (Space.pointsMap B S hS (yoneda.obj V)
              (representingIso (𝒲 := (schemeStack.{u, w} B S hS V).val) B S hS
                (yoneda.obj V) (yoneda.obj V) eV eV').hom ν))) =
      Space.localRingDimension B S hS
        (Space.pointsMap B S hS Q (selfIntersectionSourceMap B S hS V g T Q eV eQ)
          (Space.pointsMap B S hS (yoneda.obj V)
            (selfIntersectionDiagonalMap B S hS V g T Q eV eQ δ) ν)) := by
    have hcancel : Space.pointsMap B S hS Q (selfIntersectionSourceMap B S hS V g T Q eV' eQ')
          (Space.pointsMap B S hS Q
            (representingIso (𝒲 := T.pt.val) B S hS Q Q eQ eQ').hom
            (Space.pointsMap B S hS (yoneda.obj V)
              (selfIntersectionDiagonalMap B S hS V g T Q eV eQ δ) ν)) =
        Space.pointsMap B S hS (yoneda.obj V)
          (representingIso (𝒲 := (schemeStack.{u, w} B S hS V).val) B S hS
            (yoneda.obj V) (yoneda.obj V) eV eV').hom
          (Space.pointsMap B S hS Q (selfIntersectionSourceMap B S hS V g T Q eV eQ)
            (Space.pointsMap B S hS (yoneda.obj V)
              (selfIntersectionDiagonalMap B S hS V g T Q eV eQ δ) ν)) :=
      by simp only [← Space.pointsMap_comp_apply, Category.assoc, hsource]
    rw [hpt, hcancel]
    exact Space.localRingDimension_pointsMap_iso_hom B S hS
      (representingIso (𝒲 := (schemeStack.{u, w} B S hS V).val) B S hS
        (yoneda.obj V) (yoneda.obj V) eV eV') _
  simp only [HasRelationLocalRingDimension, hsdim, hdim]

/-- **The invariant read at every point of the chart does not depend on the comparison data.**
The universally quantified form of
`AlgebraicGeometry.Stack.hasRelationLocalRingDimension_transport_equivalence`, in which no
transport of the point is visible: the comparison automorphism of the chart is an isomorphism of
presheaves, hence a bijection on points, so quantifying over all points of the chart absorbs it.

The `∀` is what absorbs the transport, and that is also why this cannot be read as independence
of the comparison equivalence *inside* a condition whose side conditions single out one point of
the chart: the conditions of Stacks 0DS9 therefore fix that equivalence rather than quantify over
it. What this is for is comparing the invariant at a presentation some construction hands you
with the invariant at the one the conditions use. -/
theorem forall_hasRelationLocalRingDimension_transport_equivalence
    (hT : Bicategory.IsTwoFibreProduct T)
    (δ δ' : Bicategory.TwoCommSq.PreHom (selfIntersectionDiagonalSquare B S hS V g) T)
    (d : ℤ) :
    (∀ ν : Space.points B S hS (yoneda.obj V),
        HasRelationLocalRingDimension B S hS V g T Q eV eQ
          (Space.pointsMap B S hS (yoneda.obj V)
            (selfIntersectionDiagonalMap B S hS V g T Q eV eQ δ) ν) d) ↔
      ∀ ν : Space.points B S hS (yoneda.obj V),
        HasRelationLocalRingDimension B S hS V g T Q eV' eQ'
          (Space.pointsMap B S hS (yoneda.obj V)
            (selfIntersectionDiagonalMap B S hS V g T Q eV' eQ' δ') ν) d := by
  refine ⟨fun h ν => ?_, fun h ν =>
    (hasRelationLocalRingDimension_transport_equivalence B S hS V g T Q
      eV eV' eQ eQ' hT δ δ' ν d).2 (h _)⟩
  have hν : Space.pointsMap B S hS (yoneda.obj V)
        (representingIso (𝒲 := (schemeStack.{u, w} B S hS V).val) B S hS
          (yoneda.obj V) (yoneda.obj V) eV eV').hom
        (Space.pointsMap B S hS (yoneda.obj V)
          (representingIso (𝒲 := (schemeStack.{u, w} B S hS V).val) B S hS
            (yoneda.obj V) (yoneda.obj V) eV eV').inv ν) = ν := by
    rw [← Space.pointsMap_comp_apply, Iso.inv_hom_id, Space.pointsMap_id_apply]
  have key := (hasRelationLocalRingDimension_transport_equivalence B S hS V g T Q
    eV eV' eQ eQ' hT δ δ'
    (Space.pointsMap B S hS (yoneda.obj V)
      (representingIso (𝒲 := (schemeStack.{u, w} B S hS V).val) B S hS
        (yoneda.obj V) (yoneda.obj V) eV eV').inv ν) d).1
    (h _)
  rwa [hν] at key

end Transport

end AlgebraicGeometry.Stack

end
