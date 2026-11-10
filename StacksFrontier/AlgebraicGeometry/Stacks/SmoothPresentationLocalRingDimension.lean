module

public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Jacobson.Ideal
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.CohenMacaulay.Source
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.LocalRingGeometricStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothSourceLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentedTwoFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasScheme
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Coverings
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap
public import StacksFrontier.RingTheory.RegularLocalRing.FlatLocalHom

/-!
# The dimension of the local ring of an algebraic stack (Stacks 0DS8, Stacks 0DS9, Stacks 0DSA)

Let `𝒳` be a locally Noetherian algebraic stack over `S`, let `U` be a scheme over `S` and let
`f : U ⟶ 𝒳` be smooth. Write `R = U ×_𝒳 U` for the self-intersection, with source projection
`s = pr₁ : R ⟶ U` and target projection `t = pr₀ : R ⟶ U`, and write `R_u` for the fibre of `s`
over a point `u` of `U`. **Stacks 0DS8** states that at a geometric point `ū` of `U` with
identity arrow `e(ū)` of `R`,

`dim(𝒪_{U,ū}) - dim(𝒪_{R_u, e(ū)}) = 2 dim(𝒪_{U,ū}) - dim(𝒪_{R, e(ū)})`,

so that the invariant `2 dim(𝒪_{U,ū}) - dim(𝒪_{R, e(ū)})` of Stacks 0DSA may be computed from
the source fibre. Both sides are a rearrangement of the one input of the source's proof: `s` is
smooth, hence flat, so `𝒪_{U,ū} ⟶ 𝒪_{R, r}` is a flat local homomorphism of Noetherian local
rings and the dimension formula of Stacks 00ON applies.

**Stacks 0DS9** is the next lemma of the same section. It says that the value `d` of that
invariant depends on none of the choices entering it: at a finite type point `x` of `𝒳`, *some*
smooth chart with a finite type point above `x` realizes `d` exactly when *every* one does.
Two of the choices are settled here — the geometric point `ū` above a point of the relation, and,
through `AlgebraicGeometry.Space.localRingDimension`, the étale chart on which each of the two
dimensions is measured — so the invariant is a well-defined integer attached to a point of the
relation. The remaining choice, the smooth chart itself, is *not* settled here; see the
implementation notes.

**Stacks 0DSA** is the definition the two lemmas are for: the dimension of the local ring of `𝒳`
at a finite type point `x` *is* `d ∈ 𝐙` when the equivalent conditions of Stacks 0DS9 hold at
`x` and `d`. The legacy relation below has an extra arbitrary chart equivalence, so it is not
the faithful tagged definition; the corrected relation is in `LocalRingDimensionChartIndependence`.

## Main definitions

* `AlgebraicGeometry.Stack.HasChartLocalRingDimension`: the invariant of Stacks 0DSA measured by
  a presented self-intersection at a geometric point of the relation, as an integer.
* `AlgebraicGeometry.Stack.HasRelationLocalRingDimension`: the same invariant read off a point of
  the relation through the dimension of the local ring of Stacks 04NA.
* `AlgebraicGeometry.Stack.selfIntersectionDiagonalSquare` and
  `AlgebraicGeometry.Stack.selfIntersectionDiagonalMap`: the tautological 2-commutative square
  over the cospan `(f, f)` and the diagonal `e : U ⟶ R` it induces on representing presheaves.
* `AlgebraicGeometry.Stack.HasLocalRingDimension`: an **older, more permissive candidate** for
  Stacks 0DSA, retained without the tag because its arbitrary chart equivalence can change `d`.

## Main results

* `AlgebraicGeometry.Stack.ringKrullDim_relation_eq_add_ringKrullDim_sourceFibre`: the dimension
  of the relation at a geometric point is the dimension of the chart at its image under `s` plus
  the dimension of the fibre of `s`.
* `AlgebraicGeometry.Stack.ringKrullDim_chart_add_relation_eq`: the identity of Stacks 0DS8.
* `AlgebraicGeometry.Stack.hasChartLocalRingDimension_iff_hasRelationLocalRingDimension`: the
  invariant depends only on the point of the relation that the geometric point lies over.
* `AlgebraicGeometry.Stack.exists_hasChartLocalRingDimension`: **Stacks 0DS9**, that the invariant
  of its two conditions is a well-defined integer at a smooth chart of a locally Noetherian
  algebraic stack.
* `AlgebraicGeometry.Stack.hasChartLocalRingDimension_unique`: it determines the integer.
* `AlgebraicGeometry.Stack.exists_iff_forall_geometricPoint_hasChartLocalRingDimension`:
  **Stacks 0DS9** for the choice of geometric point — the existential and the universal condition
  over the geometric points above a point of the relation are equivalent.
* `AlgebraicGeometry.Stack.exists_hasLocalRingDimension`: existence for the **legacy**
  presentation-dependent relation. The canonical existence theorem is
  `AlgebraicGeometry.Stack.exists_hasLocalRingDimensionAtSomeChart`.

## Implementation notes

The local rings are the étale local rings `AlgebraicGeometry.Space.etaleLocalRing` at geometric
points, which is what `𝒪_{U,ū}` means in the source: the bar denotes a geometric point and the
ring is the strictly henselian one of Stacks 04KG, not the Zariski local ring.

The relation is presented by an arbitrary 2-fibre product square over the cospan `(f, f)` of
algebraic stacks and an arbitrary equivalence presenting its apex by an algebraic space `R`,
rather than by a chosen model, so the statements do not depend on either choice. The source
projection is then the morphism of representing presheaves of Stacks 04SW induced by the second
leg of the square, which is `pr₁`, hence `s`; see
`AlgebraicGeometry.Stack.SelfIntersection.relationSource` for the same morphism in the chosen
model.

The conclusions are stated at an arbitrary geometric point `r` of `R` rather than only at the
identity section `e(ū)`, which it specialises to: the input to the source's proof is flatness of
`s`, which holds at every point. The chart point is then `s(r)`, and the fibre is the fibre of
`s` — not of `t` — over `s(r)`, matching the source's `R_u`.

The fibre's local ring is presented as the quotient of `𝒪_{R,r}` by the ideal generated by the
image of the maximal ideal of `𝒪_{U,s(r)}`, written with `Ideal.jacobson` of `⊥` so that no
`IsLocalRing` instance is needed to state it; the two agree by
`IsLocalRing.jacobson_eq_maximalIdeal`.

Dimensions are `ringKrullDim`-valued, i.e. in `WithBot ℕ∞`, which has no subtraction fit to
express the source's two differences. The identity is therefore recorded in the equivalent
subtraction-free form obtained by adding `dim(𝒪_{R_u,r}) + dim(𝒪_{R,r})` to both sides,
`dim(𝒪_{U,s(r)}) + dim(𝒪_{R,r}) = 2 dim(𝒪_{U,s(r)}) + dim(𝒪_{R_u,r})`.

The invariant of Stacks 0DSA is therefore not recorded as a subtraction of `ringKrullDim`s but as
the predicate `AlgebraicGeometry.Stack.HasChartLocalRingDimension`, which names the two dimensions
as natural numbers before subtracting in `ℤ`. Both dimensions are finite — each ring is a
Noetherian local ring, so Krull's height theorem bounds its dimension — and that is exactly
`AlgebraicGeometry.Stack.exists_hasChartLocalRingDimension`, which together with
`AlgebraicGeometry.Stack.hasChartLocalRingDimension_unique` makes the predicate single out one
integer. Negative values do occur (Stacks 0DS5), which is why the codomain is `ℤ` and not `ℕ`.

**What of Stacks 0DS9 is proved, and what is not.** Its two conditions quantify over a smooth
chart `U ⟶ 𝒳`, a finite type point `u ∈ U` above `x`, the geometric point `ū` above `u` and the
model `R` of `U ×_𝒳 U`. The geometric point is settled by
`AlgebraicGeometry.Stack.exists_iff_forall_geometricPoint_hasChartLocalRingDimension`: both
dimensions are the dimension of the local ring of an algebraic space at the image point, by the
comparison of **Stacks 04N9** between the stalk at a geometric point and that dimension, so the
invariant is a function of the point of the relation alone — this is the step for which the source
cites More on Algebra, Section 15.46 (**Stacks 07QL**), that a strict henselization has the same
dimension. The étale chart on which each dimension is measured is settled with it, by
**Stacks 0BAM**.

Independence of the *smooth chart* is not proved. The source's argument shrinks `U` and `U'` so
that the two points become closed, passes to a surjective étale `W ⟶ U ×_𝒳 U'` with a closed
point above both, reduces to a smooth morphism of neighbourhoods `(U', u') ⟶ (U, u)`, and there
uses flatness together with `dim(𝒪_{U'_u ×_u U'_u, (ū',ū')}) = 2 dim(𝒪_{U'_u, ū'})` — valid at a
closed point, by Varieties Lemmas **Stacks 0B2M** and **Stacks 0A21**, and false at a generic one.
The two Varieties inputs are available, but none of the three geometric steps is, so neither the
implication from the existential to the universal condition over charts nor its converse — which
additionally needs a smooth chart carrying a finite type point above `x`, the implication of
**Stacks 06FX** that `AlgebraicGeometry.Stack.isFiniteTypePoint_of_exists_isClosed_smoothChart`
does not prove — is stated here.

**Historical candidate for Stacks 0DSA.** The source says the dimension at `x` is `d` when
the conditions of Stacks 0DS9 are satisfied. The old predicate
`AlgebraicGeometry.Stack.HasLocalRingDimension` introduces an additional existential chart
equivalence and is **not** the eventual faithful definition. The later relation
`AlgebraicGeometry.Stack.HasLocalRingDimensionAtSomeChart` fixes that equivalence canonically;
its uniqueness is proved in `LocalRingDimensionChartComparison`. Local Noetherianity of `𝒳` and
finite-typeness of `x` are arguments of the predicate but are used in neither body, as in
`AlgebraicGeometry.Stack.dimensionAtPoint` of Stacks 0AFN: they are what gives the defining
condition content.

Condition (1) names `𝒪_{R, e(ū)}` at the identity arrow, so it needs the diagonal `e : U ⟶ R`.
A 2-fibre product is a terminal 2-commutative square, hence receives from the tautological
square `AlgebraicGeometry.Stack.selfIntersectionDiagonalSquare` a mediating morphism of squares
unique up to the 2-cell equivalence (`CategoryTheory.Bicategory.twoFibreProductPreHom_rel`), and
`e` is the morphism of representing presheaves that mediating morphism induces. The defining
condition quantifies over that mediating morphism rather than selecting a representative of its
class, so nothing in the predicate is chosen. The point of the relation at which the invariant
is then read is `e(u)`, and `AlgebraicGeometry.Stack.HasRelationLocalRingDimension` there is the
condition at every geometric point `e(ū)` above it, by
`AlgebraicGeometry.Stack.hasChartLocalRingDimension_iff_hasRelationLocalRingDimension`.

## References

* [Stacks Project, Tag 00ON](https://stacks.math.columbia.edu/tag/00ON)
* [Stacks Project, Tag 04N9](https://stacks.math.columbia.edu/tag/04N9)
* [Stacks Project, Tag 04NA](https://stacks.math.columbia.edu/tag/04NA)
* [Stacks Project, Tag 06FX](https://stacks.math.columbia.edu/tag/06FX)
* [Stacks Project, Tag 07QL](https://stacks.math.columbia.edu/tag/07QL)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
* [Stacks Project, Tag 0AFN](https://stacks.math.columbia.edu/tag/0AFN)
* [Stacks Project, Tag 0B2M](https://stacks.math.columbia.edu/tag/0B2M)
* [Stacks Project, Tag 0BAM](https://stacks.math.columbia.edu/tag/0BAM)
* [Stacks Project, Tag 0DS8](https://stacks.math.columbia.edu/tag/0DS8)
* [Stacks Project, Tag 0DS9](https://stacks.math.columbia.edu/tag/0DS9)
* [Stacks Project, Tag 0DSA](https://stacks.math.columbia.edu/tag/0DSA)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : AlgebraicStacks.{u, w} B S hS} (U : BigFppfOver B S hS)
  (f : schemeStack.{u, w} B S hS U ⟶ 𝒳) (sq : Bicategory.TwoCommSq f f)
  (R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (eU : StacksRepresentableCFG.EquivalenceOver
    (schemeStack.{u, w} B S hS U).val.val.p
    (presheafOfCategories (yoneda.obj U ⋙ typeToCat)).p)
  (eR : StacksRepresentableCFG.EquivalenceOver
    sq.pt.val.val.p (presheafOfCategories (R ⋙ typeToCat)).p)

/-- The **source morphism** `s : R ⟶ U` of a presented self-intersection `R = U ×_𝒳 U`: the
morphism of representing presheaves of Stacks 04SW induced by the second leg `pr₁` of the
2-fibre product square. -/
noncomputable abbrev selfIntersectionSourceMap : R ⟶ yoneda.obj U :=
  representingMap B S hS sq.pt.val (schemeStack.{u, w} B S hS U).val R (yoneda.obj U) eR eU
    sq.snd.hom

/-- The étale local ring `𝒪_{U, s(r)}` of the chart at the image of a geometric point `r` of the
relation under the source morphism. -/
noncomputable abbrev chartEtaleLocalRing (r : Space.GeometricPoint B S hS R) : Type (u + 1) :=
  Space.etaleLocalRing B S hS (yoneda.obj U)
    (Space.geometricPointMap (selfIntersectionSourceMap B S hS U f sq R eU eR) r)

/-- The étale local ring `𝒪_{R_u, r}` of the fibre of the source morphism over `u = s(r)`, as the
closed fibre of `𝒪_{U, s(r)} ⟶ 𝒪_{R, r}`: the quotient of `𝒪_{R, r}` by the ideal generated by
the image of the maximal ideal of `𝒪_{U, s(r)}`. -/
noncomputable abbrev sourceFibreEtaleLocalRing (hR : IsAlgebraicSpace B S hS R)
    (r : Space.GeometricPoint B S hS R) : Type (u + 1) :=
  Space.etaleLocalRing B S hS R r ⧸
    Ideal.map (Space.etaleLocalRingMap hR (selfIntersectionSourceMap B S hS U f sq R eU eR) r)
      (⊥ : Ideal (chartEtaleLocalRing B S hS U f sq R eU eR r)).jacobson

/-- The source morphism `s : R ⟶ U` of a presented self-intersection of a smooth 1-morphism is a
smooth morphism of algebraic spaces: the second leg of the 2-fibre product square is a base
change of `f` by Stacks 075W, and Stacks 06FM reads that off on representing presheaves. -/
theorem isSmooth_selfIntersectionSourceMap
    (hf : AlgebraicStacks.IsSmooth B S hS f) (hsq : Bicategory.IsTwoFibreProduct sq)
    (hR : IsAlgebraicSpace B S hS R) :
    Space.IsSmooth B S hS (selfIntersectionSourceMap B S hS U f sq R eU eR) :=
  (hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS
      (fun _ _ k => Space.IsSmooth B S hS k)
      (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS) sq.pt.property
      (schemeStack.{u, w} B S hS U).property R (yoneda.obj U) hR
      (isAlgebraicSpace_yoneda B S hS U) eR eU sq.snd.hom).mp
    (AlgebraicStacks.isSmooth_baseChange B S hS f f sq.swap
      (Bicategory.isTwoFibreProduct_swap hsq) hf)

/-- The chart of a smooth 1-morphism to a locally Noetherian algebraic stack has the étale-local
property of local Noetherianity, by the scheme criterion of Stacks 04YF. -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_chart
    (hf : AlgebraicStacks.IsSmooth B S hS f)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳) :
    Space.HasEtaleLocalProperty B S hS (yoneda.obj U)
      (fun T : Scheme.{u} => IsLocallyNoetherian T) := by
  have hUloc : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U) := by
    let : ObjectProperty.IsLocal (fun T : Scheme.{u} => IsLocallyNoetherian T)
        (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})) :=
      ObjectProperty.IsLocal.of_le Scheme.smoothPrecoverage_le_fppfPrecoverage
    exact (exists_scheme_atlas_iff_forall_scheme.{u, w} B S hS
      (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒳).mp h𝒳 U f hf
  exact (Space.exists_atlas_iff_of_representable B S hS (yoneda.obj U)
    (fun T : Scheme.{u} => IsLocallyNoetherian T) U (Iso.refl _)).2 hUloc

/-- The étale local rings of the chart at `s(r)` and of the relation at `r` are Noetherian local
rings. -/
private theorem isLocalRing_and_isNoetherianRing_etaleLocalRings
    (hf : AlgebraicStacks.IsSmooth B S hS f) (hsq : Bicategory.IsTwoFibreProduct sq)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳) (hR : IsAlgebraicSpace B S hS R)
    (r : Space.GeometricPoint B S hS R) :
    IsLocalRing (chartEtaleLocalRing B S hS U f sq R eU eR r) ∧
      IsLocalRing (Space.etaleLocalRing B S hS R r) ∧
      IsNoetherianRing (chartEtaleLocalRing B S hS U f sq R eU eR r) ∧
      IsNoetherianRing (Space.etaleLocalRing B S hS R r) := by
  have hUy : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  have hs : Space.IsSmooth B S hS (selfIntersectionSourceMap B S hS U f sq R eU eR) :=
    isSmooth_selfIntersectionSourceMap B S hS U f sq R eU eR hf hsq hR
  have hUetale : Space.HasEtaleLocalProperty B S hS (yoneda.obj U)
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
    hasEtaleLocalProperty_isLocallyNoetherian_chart B S hS U f hf h𝒳
  have hRetale : Space.HasEtaleLocalProperty B S hS R
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
    Space.isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hR hUy _
      (Space.isLocallyOfFiniteType_of_isSmooth B S hS hs) hUetale
  exact ⟨Space.isLocalRing_etaleLocalRing B S hS (yoneda.obj U) hUy _,
    Space.isLocalRing_etaleLocalRing B S hS R hR r,
    Space.isNoetherianRing_etaleLocalRing_of_isLocallyNoetherian B S hS (yoneda.obj U) hUy
      hUetale _,
    Space.isNoetherianRing_etaleLocalRing_of_isLocallyNoetherian B S hS R hR hRetale r⟩

/-- **Stacks 0DS8**, the dimension formula. For a smooth 1-morphism `f : U ⟶ 𝒳` from a scheme to
a locally Noetherian algebraic stack and a presented self-intersection `R = U ×_𝒳 U` with source
morphism `s`, the dimension of `𝒪_{R, r}` at a geometric point `r` is the sum of the dimension
of `𝒪_{U, s(r)}` and the dimension of the fibre `𝒪_{R_{s(r)}, r}`.

The morphism `s` is smooth, hence flat, so `𝒪_{U, s(r)} ⟶ 𝒪_{R, r}` is a flat local
homomorphism of Noetherian local rings and Stacks 00ON applies. -/
@[stacks 0DS8 "the dimension formula for the source projection"]
theorem ringKrullDim_relation_eq_add_ringKrullDim_sourceFibre
    (hf : AlgebraicStacks.IsSmooth B S hS f) (hsq : Bicategory.IsTwoFibreProduct sq)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳) (hR : IsAlgebraicSpace B S hS R)
    (r : Space.GeometricPoint B S hS R) :
    ringKrullDim (Space.etaleLocalRing B S hS R r) =
      ringKrullDim (chartEtaleLocalRing B S hS U f sq R eU eR r) +
        ringKrullDim (sourceFibreEtaleLocalRing B S hS U f sq R eU eR hR r) := by
  have hUy : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  have hs : Space.IsSmooth B S hS (selfIntersectionSourceMap B S hS U f sq R eU eR) :=
    isSmooth_selfIntersectionSourceMap B S hS U f sq R eU eR hf hsq hR
  obtain ⟨_, _, _, _⟩ :=
    isLocalRing_and_isNoetherianRing_etaleLocalRings B S hS U f sq R eU eR hf hsq h𝒳 hR r
  let : Algebra (chartEtaleLocalRing B S hS U f sq R eU eR r)
      (Space.etaleLocalRing B S hS R r) :=
    (Space.etaleLocalRingMap hR (selfIntersectionSourceMap B S hS U f sq R eU eR) r).toAlgebra
  have : IsLocalHom (algebraMap (chartEtaleLocalRing B S hS U f sq R eU eR r)
      (Space.etaleLocalRing B S hS R r)) :=
    Space.isLocalHom_etaleLocalRingMap B S hS hR hUy _ r
  have hflat : Module.Flat (chartEtaleLocalRing B S hS U f sq R eU eR r)
      (Space.etaleLocalRing B S hS R r) :=
    Space.flat_etaleLocalRingMap B S hS hR hUy _
      (Space.isFlat_of_isSmooth B S hS _ hs) r
  have hjac : (⊥ : Ideal (chartEtaleLocalRing B S hS U f sq R eU eR r)).jacobson =
      IsLocalRing.maximalIdeal (chartEtaleLocalRing B S hS U f sq R eU eR r) :=
    IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top
  show ringKrullDim (Space.etaleLocalRing B S hS R r) =
    ringKrullDim (chartEtaleLocalRing B S hS U f sq R eU eR r) +
      ringKrullDim (Space.etaleLocalRing B S hS R r ⧸
        Ideal.map (Space.etaleLocalRingMap hR
            (selfIntersectionSourceMap B S hS U f sq R eU eR) r)
          (⊥ : Ideal (chartEtaleLocalRing B S hS U f sq R eU eR r)).jacobson)
  rw [hjac]
  exact ringKrullDim_eq_add_ringKrullDim_closedFibre _ _ hflat

/-- **Stacks 0DS8.** The identity
`dim(𝒪_{U,s(r)}) - dim(𝒪_{R_u,r}) = 2 dim(𝒪_{U,s(r)}) - dim(𝒪_{R,r})`, recorded in the
subtraction-free form obtained by adding `dim(𝒪_{R_u,r}) + dim(𝒪_{R,r})` to both sides, which is
equivalent to it wherever the three dimensions are finite — in particular here, all three rings
being Noetherian local.

The invariant `2 dim(𝒪_{U,s(r)}) - dim(𝒪_{R,r})` of Stacks 0DSA is thus computed by the source
fibre. -/
@[stacks 0DS8 "the dimension-difference identity"]
theorem ringKrullDim_chart_add_relation_eq
    (hf : AlgebraicStacks.IsSmooth B S hS f) (hsq : Bicategory.IsTwoFibreProduct sq)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳) (hR : IsAlgebraicSpace B S hS R)
    (r : Space.GeometricPoint B S hS R) :
    ringKrullDim (chartEtaleLocalRing B S hS U f sq R eU eR r) +
        ringKrullDim (Space.etaleLocalRing B S hS R r) =
      ringKrullDim (chartEtaleLocalRing B S hS U f sq R eU eR r) +
          ringKrullDim (chartEtaleLocalRing B S hS U f sq R eU eR r) +
        ringKrullDim (sourceFibreEtaleLocalRing B S hS U f sq R eU eR hR r) := by
  rw [ringKrullDim_relation_eq_add_ringKrullDim_sourceFibre B S hS U f sq R eU eR hf hsq h𝒳 hR r,
    add_assoc]

/-! ### Stacks 0DS9: the invariant of Stacks 0DSA is a well-defined integer -/

/-- **The invariant of Stacks 0DSA.** The integer `d = 2 dim(𝒪_{U,s(r)}) - dim(𝒪_{R,r})` measured
by a presented self-intersection `R = U ×_𝒳 U` at a geometric point `r` of the relation.

The two dimensions are named as natural numbers before the difference is taken, because
`ringKrullDim` takes values in `WithBot ℕ∞`, which has no subtraction fit to express it;
`AlgebraicGeometry.Stack.exists_hasChartLocalRingDimension` is their finiteness. -/
def HasChartLocalRingDimension (r : Space.GeometricPoint B S hS R) (d : ℤ) : Prop :=
  ∃ m n : ℕ,
    ringKrullDim (chartEtaleLocalRing B S hS U f sq R eU eR r) = (m : WithBot ℕ∞) ∧
      ringKrullDim (Space.etaleLocalRing B S hS R r) = (n : WithBot ℕ∞) ∧
        2 * (m : ℤ) - (n : ℤ) = d

/-- The invariant of Stacks 0DSA read off a point `ρ` of the relation instead of a geometric point
above it: the dimension of the local ring of **Stacks 04NA** of the chart at the image of `ρ`
under the source morphism, and of the relation at `ρ`. -/
def HasRelationLocalRingDimension (ρ : Space.points B S hS R) (d : ℤ) : Prop :=
  ∃ m n : ℕ,
    Space.localRingDimension B S hS
        (Space.pointsMap B S hS R (selfIntersectionSourceMap B S hS U f sq R eU eR) ρ) =
        (m : ℕ∞) ∧
      Space.localRingDimension B S hS ρ = (n : ℕ∞) ∧ 2 * (m : ℤ) - (n : ℤ) = d

/-- **The invariant depends only on the point of the relation**, not on the geometric point above
it nor on the étale charts measuring the two dimensions: by the comparison step of **Stacks 04N9**
each `ringKrullDim` of a stalk at a geometric point is the dimension of the local ring of
**Stacks 04NA** of the algebraic space at the image point. -/
theorem hasChartLocalRingDimension_iff_hasRelationLocalRingDimension
    (hR : IsAlgebraicSpace B S hS R) (r : Space.GeometricPoint B S hS R) (d : ℤ) :
    HasChartLocalRingDimension B S hS U f sq R eU eR r d ↔
      HasRelationLocalRingDimension B S hS U f sq R eU eR r.image d := by
  have h₁ : ringKrullDim (Space.etaleLocalRing B S hS R r) =
      (Space.localRingDimension B S hS r.image : WithBot ℕ∞) :=
    Space.ringKrullDim_etaleLocalRing_eq_localRingDimension hR r
  have h₂ : ringKrullDim (chartEtaleLocalRing B S hS U f sq R eU eR r) =
      (Space.localRingDimension B S hS
        (Space.pointsMap B S hS R (selfIntersectionSourceMap B S hS U f sq R eU eR) r.image) :
          WithBot ℕ∞) :=
    Space.ringKrullDim_etaleLocalRing_eq_localRingDimension (isAlgebraicSpace_yoneda B S hS U)
      (Space.geometricPointMap (selfIntersectionSourceMap B S hS U f sq R eU eR) r)
  constructor <;> rintro ⟨m, n, hm, hn, hd⟩
  · exact ⟨m, n, by exact_mod_cast h₂.symm.trans hm, by exact_mod_cast h₁.symm.trans hn, hd⟩
  · exact ⟨m, n, h₂.trans (by exact_mod_cast hm), h₁.trans (by exact_mod_cast hn), hd⟩

/-- **Stacks 0DS9, for the choice of geometric point.** The existential and the universal
condition over the geometric points above a point `ρ` of the relation are equivalent: some
geometric point above `ρ` measures the invariant to be `d` exactly when every one does.

Forward this is
`AlgebraicGeometry.Stack.hasChartLocalRingDimension_iff_hasRelationLocalRingDimension`; backward
it is the existence of a geometric point above `ρ`. -/
@[stacks 0DS9 "the two conditions, over the geometric point above a point of the relation"]
theorem exists_iff_forall_geometricPoint_hasChartLocalRingDimension
    (hR : IsAlgebraicSpace B S hS R) (ρ : Space.points B S hS R) (d : ℤ) :
    (∃ r : Space.GeometricPoint B S hS R, r.LiesOver ρ ∧
        HasChartLocalRingDimension B S hS U f sq R eU eR r d) ↔
      ∀ r : Space.GeometricPoint B S hS R, r.LiesOver ρ →
        HasChartLocalRingDimension B S hS U f sq R eU eR r d := by
  constructor
  · rintro ⟨r, rfl, hr⟩ r' hr'
    refine (hasChartLocalRingDimension_iff_hasRelationLocalRingDimension
      B S hS U f sq R eU eR hR r' d).2 ?_
    rw [show r'.image = r.image from hr']
    exact (hasChartLocalRingDimension_iff_hasRelationLocalRingDimension
      B S hS U f sq R eU eR hR r d).1 hr
  · intro h
    obtain ⟨r, hr⟩ := Space.exists_geometricRepresentative B S hS R ρ
    exact ⟨r, hr, h r hr⟩

/-- **Stacks 0DS9, well-definedness of the invariant.** At a geometric point of a presented
self-intersection of a smooth chart of a locally Noetherian algebraic stack the invariant
`2 dim(𝒪_{U,s(r)}) - dim(𝒪_{R,r})` of Stacks 0DSA is realized by an integer: both local rings are
Noetherian local rings, so Krull's height theorem makes both dimensions finite.

This is what lets the conditions of Stacks 0DS9 be read at a `d ∈ ℤ`; the integer is unique by
`AlgebraicGeometry.Stack.hasChartLocalRingDimension_unique`. -/
@[stacks 0DS9 "the invariant of the two conditions is a well-defined integer at a smooth chart"]
theorem exists_hasChartLocalRingDimension
    (hf : AlgebraicStacks.IsSmooth B S hS f) (hsq : Bicategory.IsTwoFibreProduct sq)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳) (hR : IsAlgebraicSpace B S hS R)
    (r : Space.GeometricPoint B S hS R) :
    ∃ d : ℤ, HasChartLocalRingDimension B S hS U f sq R eU eR r d := by
  have hUy : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  have hs : Space.IsSmooth B S hS (selfIntersectionSourceMap B S hS U f sq R eU eR) :=
    isSmooth_selfIntersectionSourceMap B S hS U f sq R eU eR hf hsq hR
  obtain ⟨_, _, _, _⟩ :=
    isLocalRing_and_isNoetherianRing_etaleLocalRings B S hS U f sq R eU eR hf hsq h𝒳 hR r
  obtain ⟨m, hm⟩ :=
    Stacks.RegularLocalRing.KernelRegularity.exists_natCast_eq_ringKrullDim
      (chartEtaleLocalRing B S hS U f sq R eU eR r)
  obtain ⟨n, hn⟩ :=
    Stacks.RegularLocalRing.KernelRegularity.exists_natCast_eq_ringKrullDim
      (Space.etaleLocalRing B S hS R r)
  exact ⟨2 * (m : ℤ) - (n : ℤ), m, n, hm, hn, rfl⟩

/-- The invariant of Stacks 0DSA determines the integer it is measured to be. -/
theorem hasChartLocalRingDimension_unique (r : Space.GeometricPoint B S hS R) {d e : ℤ}
    (hd : HasChartLocalRingDimension B S hS U f sq R eU eR r d)
    (he : HasChartLocalRingDimension B S hS U f sq R eU eR r e) : d = e := by
  obtain ⟨m, n, hm, hn, hd'⟩ := hd
  obtain ⟨m', n', hm', hn', he'⟩ := he
  have hmm : m = m' := by exact_mod_cast hm.symm.trans hm'
  have hnn : n = n' := by exact_mod_cast hn.symm.trans hn'
  omega

/-! ### Stacks 0DSA: the dimension of the local ring at a finite type point -/

/-- The **tautological 2-commutative square** over the cospan `(f, f)`: its apex is the source of
`f` and both its projections are the identity, filled by the identity 2-morphism. A mediating
1-morphism from it into a 2-fibre product `R = U ×_𝒳 U` is the diagonal `e : U ⟶ R`. -/
def selfIntersectionDiagonalSquare : Bicategory.TwoCommSq f f where
  pt := schemeStack.{u, w} B S hS U
  fst := 𝟙 _
  snd := 𝟙 _
  iso := Iso.refl _

/-- The **diagonal** `e : U ⟶ R` of a presented self-intersection `R = U ×_𝒳 U`, as the morphism
of representing presheaves of Stacks 04SW induced by a morphism `δ` of 2-commutative squares from
the tautological square of `AlgebraicGeometry.Stack.selfIntersectionDiagonalSquare` into `sq`.
Terminality of a 2-fibre product makes any two such `δ` 2-cell equivalent. -/
noncomputable abbrev selfIntersectionDiagonalMap
    (δ : Bicategory.TwoCommSq.PreHom (selfIntersectionDiagonalSquare B S hS U f) sq) :
    yoneda.obj U ⟶ R :=
  representingMap B S hS (schemeStack.{u, w} B S hS U).val sq.pt.val (yoneda.obj U) R eU eR
    δ.hom.hom

/-- **Legacy candidate for Stacks 0DSA, not a single-valued dimension relation.**
The dimension of the local ring of a locally Noetherian algebraic stack `𝒳`
at a finite type point `x ∈ |𝒳|` *is* the integer `d` when condition (1) of Stacks 0DS9 holds:
some scheme `U` of the site carries a smooth 1-morphism `f : U ⟶ 𝒳` and a finite type point `u`
of `U` above `x` at which a presented self-intersection `R = U ×_𝒳 U`, with diagonal `e`, has
`2 dim(𝒪_{U,ū}) - dim(𝒪_{R, e(ū)}) = d`.

The source phrases the dimension as a relation between `x` and `d ∈ ℤ`, not as a function of `x`.
However, the arbitrary existential chart equivalence `eV` here may transport the measured point
without transporting the side condition; this relation is not necessarily single-valued.
The faithful, chart-independent relation carrying tag 0DSA is
`AlgebraicGeometry.Stack.HasLocalRingDimensionAtSomeChart`, defined in
`LocalRingDimensionChartIndependence.lean`. Retained for compatibility, not as a Stacks tag.
Negative values occur (Stacks 0DS5), whence `ℤ`. -/
def HasLocalRingDimension (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (_h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (x : points B S hS 𝒳.val.val 𝒳.val.property)
    (_hx : IsFiniteTypePoint.{u, w} B S hS 𝒳 x) (d : ℤ) : Prop :=
  ∃ (V : BigFppfOver B S hS) (g : schemeStack.{u, w} B S hS V ⟶ 𝒳)
      (T : Bicategory.TwoCommSq g g) (_hT : Bicategory.IsTwoFibreProduct T)
      (Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hQ : IsAlgebraicSpace B S hS Q)
      (eV : StacksRepresentableCFG.EquivalenceOver
        (schemeStack.{u, w} B S hS V).val.val.p
        (presheafOfCategories (yoneda.obj V ⋙ typeToCat)).p)
      (eQ : StacksRepresentableCFG.EquivalenceOver
        T.pt.val.val.p (presheafOfCategories (Q ⋙ typeToCat)).p)
      (δ : Bicategory.TwoCommSq.PreHom (selfIntersectionDiagonalSquare B S hS V g) T)
      (ν : Space.points B S hS (yoneda.obj V)),
    AlgebraicStacks.IsSmooth B S hS g ∧
      AlgebraicGeometry.IsFiniteTypePoint (Space.pointsToScheme B S hS V ν) ∧
        pointsMap B S hS (schemeFibredCategory B S hS V).val
            (schemeFibredCategory B S hS V).property 𝒳.val.property g.hom.hom
            (representedChartPointMap B S hS V ν) = x ∧
          HasRelationLocalRingDimension B S hS V g T Q eV eQ
            (Space.pointsMap B S hS (yoneda.obj V)
              (selfIntersectionDiagonalMap B S hS V g T Q eV eQ δ) ν) d

include eU eR in
/-- **Existence for the legacy presentation-dependent relation.** The old predicate
`HasLocalRingDimension` is satisfied by some integer when the point has a smooth chart with a
finite type point above it: both local rings entering the invariant are Noetherian, so their
dimensions are finite. This theorem does not establish the chart-independent relation of Stacks
0DSA; that is `exists_hasLocalRingDimensionAtSomeChart`. -/
theorem exists_hasLocalRingDimension (hf : AlgebraicStacks.IsSmooth B S hS f)
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
    ∃ d : ℤ, HasLocalRingDimension B S hS 𝒳 h𝒳 x hx d := by
  obtain ⟨r, hr⟩ := Space.exists_geometricRepresentative B S hS R
    (Space.pointsMap B S hS (yoneda.obj U)
      (selfIntersectionDiagonalMap B S hS U f sq R eU eR δ) ν)
  obtain ⟨d, hd⟩ := exists_hasChartLocalRingDimension B S hS U f sq R eU eR hf hsq h𝒳 hR r
  exact ⟨d, U, f, sq, hsq, R, hR, eU, eR, δ, ν, hf, hν, hνx,
    hr ▸ (hasChartLocalRingDimension_iff_hasRelationLocalRingDimension
      B S hS U f sq R eU eR hR r d).1 hd⟩

end AlgebraicGeometry.Stack

end
