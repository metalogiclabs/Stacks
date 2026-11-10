module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSeparablePoint
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparableChartPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointsMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.LocalRingDimension
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointSmoothChart
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothPresentationLocalRingDimension
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalRingDimensionChartIndependence
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalRingPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.MorphismSpaceSections
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalChartSmoothBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Etale
public import StacksFrontier.CategoryTheory.TwoFibreProduct.InducedBicategory
public import StacksFrontier.Deformation.Artin.ChangeOfField.SiteEquivalenceOver
public import StacksFrontier.Deformation.Artin.FiniteDimensional.TangentChart
public import StacksFrontier.Deformation.Artin.Predeformation.FormallyEtale
public import StacksFrontier.Deformation.Artin.Predeformation.SelfIntersection
public import StacksFrontier.Deformation.Artin.SliceSeparableCompletion
public import StacksFrontier.Deformation.Artin.Versality.RepresentablySmoothPredeformation
public import StacksFrontier.Deformation.CofiberedPresentation.ChartDimension

/-!
# The dimension of the local ring of an algebraic stack from a versal cogroupoid (Stacks 0DSB)

Let `𝒳` be an algebraic stack locally of finite type over a locally Noetherian scheme `S`, let
`x₀ : Spec k ⟶ 𝒳` be a morphism with `k` of finite type over `S`, and represent `𝓕_{𝒳,k,x₀}` as in
Remark 0DR3 by a cogroupoid `(A, B, s, t, c)`. Then the dimension of the local ring of `𝒳` at the
point of `x₀` (Stacks 0DSA) is `2 dim A - dim B`.

## Main results

* `AlgebraicGeometry.Stack.hasLocalRingDimension_of_versalCogroupoid`: **Stacks 0DSB**.

## Implementation notes

The proof is the general one of the source. The integer `2 dim A - dim B` does not depend on the
cogroupoid (`Deformation.twoMul_ringKrullDim_sub_eq_of_isVersal`) and is invariant under a finite
separable extension of the residue field
(`Deformation.GroupoidInFunctors.twoMul_ringKrullDim_sub_eq_of_changeOfFields`, with Stacks 07WX).
Over a suitable finite separable extension `L/k` it is computed by a smooth chart `V ⟶ 𝒳` with a
point `ν` of residue field exactly `l ⊆ L`
(`AlgebraicGeometry.Stack.exists_smoothChart_point_residueField_eq`): the deformations of the
`L`-point of `V` over `ν` are prorepresented by a ring of dimension `dim 𝒪_{V,ν}`, the
self-`2`-fibre product of the induced smooth functor is the deformation category of the diagonal
point of `R = V ×_𝒳 V` (Stacks 07WL), which is that of a point `w` of an étale chart `W` of the
algebraic space `R` (`AlgebraicGeometry.Stack.exists_etaleChart_point_isSeparable_selfIntersection`
and `Deformation.Artin.predeformationEquivalenceOfFormallyEtale`), prorepresented by a ring of
dimension `dim 𝒪_{W,w} = dim 𝒪_{R,e(ν)}`. This is exactly the integer of Stacks 0DSA at the chart
`V`.

## References

* [Stacks Project, Tag 0DSB](https://stacks.math.columbia.edu/tag/0DSB)
* [Stacks Project, Tag 0DR3](https://stacks.math.columbia.edu/tag/0DR3)
* [Stacks Project, Tag 0DSA](https://stacks.math.columbia.edu/tag/0DSA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Deformation.Artin.SliceTangent

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The diagonal `V ⟶ V ×_𝒳 V` of the canonical self-intersection of a 1-morphism from a scheme,
as a pre-morphism of `2`-commutative squares: the mediating 1-morphism of the canonical
`2`-fibre product, with identity comparisons. -/
def selfIntersectionDiagonalPreHom {𝒳 : AlgebraicStacks.{u, w} B S hS} (V : BigFppfOver B S hS)
    (g : schemeStack.{u, w} B S hS V ⟶ 𝒳) :
    Bicategory.TwoCommSq.PreHom (selfIntersectionDiagonalSquare B S hS V g)
      (twoFibreProductSquareAlgebraicStacks B S hS g g) :=
  Bicategory.TwoCommSq.PreHom.ofUnderlying
    (CatFiberedInGroupoids.preHomTwoFibreProductSquare.{u, u, u + 1, u + 1} g.hom g.hom
      (selfIntersectionDiagonalSquare B S hS V g).underlying)

/-- A smooth 1-morphism from the algebraic stack of a scheme to an algebraic stack is relatively
smooth: it is representable by algebraic spaces (the target has representable diagonal) and
Stacks 06FM reads smoothness off the existential smooth-diagram test. -/
theorem isRelativelySmooth_of_isSmooth_schemeStack {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (V : BigFppfOver B S hS) (g : schemeStack.{u, w} B S hS V ⟶ 𝒳)
    (hg : AlgebraicStacks.IsSmooth B S hS g) : IsRelativelySmooth B S hS g.hom := by
  let smoothP : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    fun _ _ h => Space.IsSmooth B S hS h
  have hsm : Space.IsSmoothLocalOnSourceAndTarget B S hS smoothP :=
    Space.isSmoothLocalOnSourceAndTarget_smooth B S hS
  let : (spaceProperty B S hS smoothP).IsStableUnderBaseChange :=
    Space.isSmooth_isStableUnderBaseChange B S hS
  let : (spaceProperty B S hS smoothP).IsLocalAtTarget
      (Space.Topology.fpqc.precoverage.{u, u + 1} B S hS) :=
    Space.smooth_isLocalAtTarget_fpqc B S hS
  let : (spaceProperty B S hS smoothP).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u + 1} B S hS) :=
    MorphismProperty.IsLocalAtTarget.of_le
      (L := Space.Topology.fpqc.precoverage.{u, u + 1} B S hS)
      (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)
  have hrep : IsRepresentableByAlgebraicSpaces B S hS g.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒳.property
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS V) _
  exact ⟨hrep, hasRelativeProperty_of_hasPropertyOnSomeSmoothDiagram.{u, u + 1} B S hS smoothP hsm
    g.hom hrep hg⟩

/-- The section of a represented presheaf named by an object of the slice is its structure
morphism, so a 1-morphism from `(Sch/W)` sends it to the section named by its image. -/
theorem representingMap_app_hom
    (𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eQ : StacksRepresentableCFG.EquivalenceOver 𝒴.val.p (presheafOfCategories (Q ⋙ typeToCat)).p)
    (W : BigFppfOver B S hS) (k : schemeFibredCategory B S hS W ⟶ 𝒴) (u : Over W) :
    (representingMap B S hS (schemeFibredCategory B S hS W) 𝒴 (yoneda.obj W) Q
        (PresheafOfCategories.sliceElementsEquivalenceOver W) eQ k).app (op u.left) u.hom =
      PresheafOfCategories.sectionOfObj eQ ((CatFiberedInGroupoids.homFunctor k).obj u)
        (Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p k) u) := by
  have h := morphismSpaceEquiv_app_sectionOfObj B S hS (schemeFibredCategory B S hS W) 𝒴
    (yoneda.obj W) Q (PresheafOfCategories.sliceElementsEquivalenceOver W) eQ
    ⟨CatFiberedInGroupoids.homFunctor k, CatFiberedInGroupoids.homFunctor_comp_p k⟩ u
    (W := u.left) rfl
  have hs : PresheafOfCategories.sectionOfObj (PresheafOfCategories.sliceElementsEquivalenceOver W)
      u (rfl : (Over.forget W).obj u = u.left) = u.hom := by
    simpa using sectionOfObj_sliceElementsEquivalenceOver u rfl
  exact (congrArg _ hs.symm).trans h

/-- Cancelling the `eqToHom`s on both sides of an equation of morphisms. -/
private theorem eq_eqToHom_comp_comp_eqToHom {C : Type*} [Category C] {A B A' B' : C} (h : A = B)
    (h' : A' = B') {f : A ⟶ A'} {m : B ⟶ B'} (H : eqToHom h.symm ≫ f ≫ eqToHom h' = m) :
    f = eqToHom h ≫ m ≫ eqToHom h'.symm := by
  subst h h'
  simpa using H

/-- If a point `w₀` of `(Sch/W)` maps to the point `u₀` of `(Sch/V)` by a morphism `π` inducing
`l ⟶ L` on residue fields, the point of `w₀` seen in `V` is that of `u₀` precomposed with
`Spec L ⟶ Spec l`, so both have the same image of the closed point. -/
private theorem pointMap_comp_algebraMap_eq {V W : BigFppfOver B S hS} {Λ l L : Type u}
    [CommRing Λ] [Field l] [Field L] [Algebra Λ l] [Algebra Λ L] [Algebra l L]
    {iΛ : Spec (.of Λ) ⟶ S} {u₀ : Over V} {w₀ : Over W} (π : w₀.left ⟶ u₀.left)
    (hu₀ : (Over.forget V ⋙ Over.post B.inclusion).obj u₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ))
    (hw₀ : (Over.forget W ⋙ Over.post B.inclusion).obj w₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ L)) ≫ iΛ))
    (huL : (Over.forget V ⋙ Over.post B.inclusion).obj (Over.mk (π ≫ u₀.hom)) =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ L)) ≫ iΛ))
    (hπ : eqToHom (congrArg Over.left hw₀).symm ≫ B.inclusion.map π.left ≫
      eqToHom (congrArg Over.left hu₀) = Spec.map (CommRingCat.ofHom (algebraMap l L))) :
    pointMap huL = Spec.map (CommRingCat.ofHom (algebraMap l L)) ≫ pointMap hu₀ ∧
      (pointMap huL).base (closedPt (.of L)) = (pointMap hu₀).base (closedPt (.of l)) := by
  have hptL : pointMap huL = Spec.map (CommRingCat.ofHom (algebraMap l L)) ≫ pointMap hu₀ := by
    have hπ' := eq_eqToHom_comp_comp_eqToHom (congrArg Over.left hw₀) (congrArg Over.left hu₀) hπ
    simp only [pointMap]
    show _ ≫ B.inclusion.map (π.left ≫ u₀.hom.left) = _
    rw [Functor.map_comp, hπ']
    simp
  refine ⟨hptL, ?_⟩
  rw [hptL, Scheme.Hom.comp_apply]
  exact congrArg _ (Subsingleton.elim _ _)

/-- **The chart computation of the invariant (Stacks 0DSB, general case of the proof).** Given the
smooth chart point `u₀` of residue field exactly `l` and the étale chart point `w₀` over the
diagonal point of the self-intersection, over a finite separable `L ⊇ l`, the integer
`2 dim A - dim B` of a versal object is `2 dim 𝒪_{V,ν} - dim 𝒪_{W,w}`. -/
theorem twoMul_ringKrullDim_eq_of_chartPoints (D : VersalSituation.{u, w})
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (iΛ : Spec (.of Λ) ⟶ D.S) [_root_.AlgebraicGeometry.IsOpenImmersion iΛ]
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (ξ : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀).projection)
    (hξ : Deformation.IsVersal (Deformation.Artin.predeformationCategory_isPredeformationCategory
      D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property).cofibered ξ)
    (Bv : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k)
    (e : Deformation.restrictedCoyoneda Bv ≅ (Deformation.versalGroupoid
      (Deformation.Artin.predeformationCategory iΛ
        (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀).projection
      (Deformation.Artin.predeformationCategory_isPredeformationCategory
        D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property) ξ).arrows)
    {l L : Type u} [Field l] [Field L] [Algebra k l] [Algebra Λ l] [IsScalarTower Λ k l]
    [Module.Finite k l] [Algebra.IsSeparable k l] [Algebra l L] [Algebra Λ L]
    [IsScalarTower Λ l L] [Module.Finite l L] [Algebra.IsSeparable l L]
    (V : BigFppfOver D.B D.S D.hS) (g : schemeStack.{u, w} D.B D.S D.hS V ⟶ D.𝒳)
    (hg : AlgebraicStacks.IsSmooth D.B D.S D.hS g) [LocallyOfFiniteType (D.B.inclusion.map V.hom)]
    (u₀ : Over V)
    (hu₀ : (Over.forget V ⋙ Over.post D.B.inclusion).obj u₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ))
    (hxₗ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj
        ((CatFiberedInGroupoids.homFunctor g.hom).obj u₀) =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ))
    (η : (CatFiberedInGroupoids.homFunctor g.hom).obj u₀ ⟶ x₀)
    (hη : eqToHom (congrArg Over.left hxₗ).symm ≫
        ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).map η).left ≫
      eqToHom (congrArg Over.left hx₀) = Spec.map (CommRingCat.ofHom (algebraMap k l)))
    (hc₀ : ∀ c : AffineChart iΛ (D.B.inclusion.map V.hom)
        ((pointMap hu₀).base (closedPt (.of l))),
      Function.Surjective (c.ringMap (pointMap hu₀) (range_pointMap (hv₀ := hu₀) c)))
    (Q : (BigFppfOver D.B D.S D.hS)ᵒᵖ ⥤ Type u)
    (eQ : StacksRepresentableCFG.EquivalenceOver
      (twoFibreProductSquareAlgebraicStacks D.B D.S D.hS g g).pt.val.val.p
      (presheafOfCategories (Q ⋙ typeToCat)).p)
    (W : BigFppfOver D.B D.S D.hS) [LocallyOfFiniteType (D.B.inclusion.map W.hom)]
    (a : yoneda.obj W ⟶ Q)
    (ha : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme D.B D.S D.hS))) a)
    (w₀ : Over W)
    (hw₀ : (Over.forget W ⋙ Over.post D.B.inclusion).obj w₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ L)) ≫ iΛ))
    (π : w₀.left ⟶ u₀.left)
    (hπ : eqToHom (congrArg Over.left hw₀).symm ≫ D.B.inclusion.map π.left ≫
      eqToHom (congrArg Over.left hu₀) = Spec.map (CommRingCat.ofHom (algebraMap l L)))
    (hπa : yoneda.map w₀.hom ≫ a = yoneda.map π ≫ yoneda.map u₀.hom ≫
      selfIntersectionDiagonalMap D.B D.S D.hS V g
        (twoFibreProductSquareAlgebraicStacks D.B D.S D.hS g g) Q
        (PresheafOfCategories.sliceElementsEquivalenceOver V) eQ
        (selfIntersectionDiagonalPreHom D.B D.S D.hS V g)) :
    ∃ a b a' b' : ℕ, ringKrullDim ξ.base = a ∧ ringKrullDim Bv = b ∧
      ringKrullDim ((D.B.inclusion.obj V.left).presheaf.stalk
        ((pointMap hu₀).base (closedPt (.of l)))) = a' ∧
      ringKrullDim ((D.B.inclusion.obj W.left).presheaf.stalk
        ((pointMap hw₀).base (closedPt (.of L)))) = b' ∧
      2 * a + b' = 2 * a' + b := by
  have : IsLocallyNoetherian (Spec (.of Λ)) := isLocallyNoetherian_of_isOpenImmersion iΛ
  have : IsNoetherianRing Λ := (isLocallyNoetherian_Spec (R := CommRingCat.of Λ)).mp inferInstance
  -- the tower `Λ → k → L`
  let : Algebra k L := ((algebraMap l L).comp (algebraMap k l)).toAlgebra
  have : IsScalarTower k l L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower Λ k L := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply Λ l L, IsScalarTower.algebraMap_apply Λ k l]
    rfl
  have : Module.Finite k L := Module.Finite.trans l L
  have : Module.Finite Λ l := Module.Finite.trans k l
  have : Module.Finite Λ L := Module.Finite.trans k L
  have : Algebra.IsSeparable k L := Algebra.IsSeparable.trans k l L
  let T₀ : Deformation.ChangeOfFieldsSituation.{u, u, u} := { Λ := Λ, k := k, l := L }
  have hfinl := Deformation.Artin.locallyOfFiniteType_quasiCompact_of_finite (k := k) (l := l)
    iΛ hfinite
  have hfinL := Deformation.Artin.locallyOfFiniteType_quasiCompact_of_finite (k := k) (l := L)
    iΛ hfinite
  -- the point `u_L` of `V` over `Spec L`
  let uL : Over V := Over.mk (π ≫ u₀.hom)
  have huL : (Over.forget V ⋙ Over.post D.B.inclusion).obj uL =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ L)) ≫ iΛ) := hw₀
  let Φ := CatFiberedInGroupoids.homFunctor g.hom
  have hΦ : Φ ⋙ D.𝒳.val.val.p = Over.forget V := CatFiberedInGroupoids.homFunctor_comp_p g.hom
  have hF : Φ ⋙ D.𝒳.val.val.p ⋙ Over.post D.B.inclusion = Over.forget V ⋙ Over.post D.B.inclusion :=
    congrArg (fun H => H ⋙ Over.post D.B.inclusion) hΦ
  let xL := Φ.obj uL
  have hxL := Deformation.Artin.imageBasePoint (qY := D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) iΛ
    (Over.forget V ⋙ Over.post D.B.inclusion) Φ hF uL huL
  let πL : uL ⟶ u₀ := Over.homMk π rfl
  let ηL : xL ⟶ x₀ := Φ.map πL ≫ η
  have hηL : eqToHom (congrArg Over.left hxL).symm ≫
      ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).map ηL).left ≫
        eqToHom (congrArg Over.left hx₀) = Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
    have h1' := congrArg Over.Hom.left (Functor.congr_hom hF πL)
    simp only [Functor.comp_map, Over.comp_left, Over.eqToHom_left] at h1'
    have hπ' := eq_eqToHom_comp_comp_eqToHom (congrArg Over.left hw₀) (congrArg Over.left hu₀) hπ
    have hη' := eq_eqToHom_comp_comp_eqToHom (congrArg Over.left hxₗ) (congrArg Over.left hx₀) hη
    have hcomp : Spec.map (CommRingCat.ofHom (algebraMap k L)) =
        Spec.map (CommRingCat.ofHom (algebraMap l L)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap k l)) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    simp only [ηL, Functor.map_comp, Over.comp_left]
    show _ ≫ ((Over.post D.B.inclusion).map (D.𝒳.val.val.p.map (Φ.map πL))).left ≫ _ ≫ _ = _
    rw [show ((Over.post D.B.inclusion).map (D.𝒳.val.val.p.map (Φ.map πL))).left =
      ((Φ ⋙ D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).map πL).left from rfl, h1']
    show _ ≫ (_ ≫ D.B.inclusion.map π.left ≫ _) ≫ _ ≫ _ = _
    rw [hπ', hη', hcomp]
    simp
  -- Stacks 07WX
  have hRS :
      Deformation.Artin.SatisfiesRS D.B D.S D.hS D.𝒳.val.val.p D.𝒳.val.isFiberedInGroupoids :=
    Deformation.Artin.satisfiesRS_of_isAlgebraicStack D.B D.S D.hS D.𝒳
  have hcart : D.𝒳.val.val.p.IsCartesian (D.𝒳.val.val.p.map ηL) ηL := by
    have := D.𝒳.val.isFiberedInGroupoids.isStronglyCartesian_homLift (D.𝒳.val.val.p.map ηL) ηL
    infer_instance
  let E := Deformation.Artin.Site.changeOfFieldEquivalenceOver T₀ iΛ D.B D.hS D.𝒳.val.val.p
    x₀ xL hx₀ hxL ηL D.𝒳.val.property hcart hηL hfinite hRS
  -- the smooth functor of deformation categories induced by the chart
  let mF := Deformation.Artin.mapPredeformationCategory iΛ (Over.forget V ⋙ Over.post D.B.inclusion)
    (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) Φ hF uL huL
  have hsm : Deformation.IsSmooth mF.toBasedFunctor :=
    Deformation.Artin.isSmoothOnPredeformationCategories_of_isRelativelySmooth' D.B D.S D.hS g.hom
      (isRelativelySmooth_of_isSmooth_schemeStack D.B D.S D.hS V g hg) iΛ uL huL hfinL.1 hfinL.2
      inferInstance
  -- the chart of `V`
  obtain ⟨hptL, hpt⟩ := pointMap_comp_algebraMap_eq D.B D.S D.hS π hu₀ hw₀ huL hπ
  obtain ⟨c₀⟩ := nonempty_affineChart (s := D.B.inclusion.map V.hom) (iΛ := iΛ)
    (pointMap_mem_range (hv₀ := hu₀))
  let cL : AffineChart iΛ (D.B.inclusion.map V.hom) ((pointMap huL).base (closedPt (.of L))) :=
    ⟨c₀.U, c₀.isAffineOpen, by rw [hpt]; exact c₀.mem, c₀.le⟩
  have hlV : ∀ x : l, ∃ r : cL.ring, (pointValue cL).hom r = algebraMap l L x := by
    intro x
    obtain ⟨r, hr⟩ := hc₀ c₀ x
    refine ⟨r, ?_⟩
    have h1 : pointValue cL = cL.ringMap (pointMap hu₀) (range_pointMap (hv₀ := hu₀) c₀) ≫
        CommRingCat.ofHom (algebraMap l L) := by
      have hr : Set.range (pointMap hu₀).base ⊆ cL.U := range_pointMap (hv₀ := hu₀) c₀
      rw [← AffineChart.ringMap_comp cL _ _ hr (by rw [← hptL]; exact range_pointMap cL)]
      exact AffineChart.ringMap_congr cL _ _ hptL
    rw [h1]
    show algebraMap l L (c₀.ringMap (pointMap hu₀) (range_pointMap (hv₀ := hu₀) c₀) r) = _
    rw [hr]
  obtain ⟨AV, ⟨eV⟩, hAV⟩ := exists_sliceEquivalence_of_isSeparable cL hfinL.1 hfinL.2 hlV
  -- the chart of `W`, over that of `V`
  let T := twoFibreProductSquareAlgebraicStacks D.B D.S D.hS g g
  let eV₀ := PresheafOfCategories.sliceElementsEquivalenceOver V
  let δ := selfIntersectionDiagonalPreHom D.B D.S D.hS V g
  let sQ := selfIntersectionSourceMap D.B D.S D.hS V g T Q eV₀ eQ
  let hWV : W ⟶ V := yoneda.preimage (a ≫ sQ)
  have hes : selfIntersectionDiagonalMap D.B D.S D.hS V g T Q
      (PresheafOfCategories.sliceElementsEquivalenceOver V) eQ δ ≫ sQ = 𝟙 _ :=
    selfIntersectionDiagonalMap_comp_sourceMap D.B D.S D.hS V g T Q eV₀ eQ δ
  have hcompat : w₀.hom ≫ hWV = π ≫ u₀.hom := by
    apply yoneda.map_injective
    rw [Functor.map_comp, Functor.map_preimage, ← Category.assoc, hπa, Category.assoc,
      Category.assoc, hes, Category.comp_id, Functor.map_comp]
  have hptW : pointMap hw₀ ≫ D.B.inclusion.map hWV.left = pointMap huL := by
    simp only [pointMap, Category.assoc, ← Functor.map_comp]
    congr 2
    exact congrArg CommaMorphism.left hcompat
  have hfWV : D.B.inclusion.map hWV.left ≫ D.B.inclusion.map V.hom =
      D.B.inclusion.map W.hom := by
    rw [← Functor.map_comp, Over.w hWV]
  let cV' : AffineChart iΛ (D.B.inclusion.map V.hom)
      ((pointMap hw₀ ≫ D.B.inclusion.map hWV.left).base (closedPt (.of L))) :=
    ⟨cL.U, cL.isAffineOpen, by rw [hptW]; exact cL.mem, cL.le⟩
  have hrange : Set.range (pointMap hw₀ ≫ D.B.inclusion.map hWV.left).base ⊆ cV'.U := by
    rintro _ ⟨z, rfl⟩
    obtain rfl : z = closedPt (.of L) := Subsingleton.elim _ _
    exact cV'.mem
  obtain ⟨cW, hptW', ρ, hρ⟩ := exists_affineChart_comp (D.B.inclusion.map hWV.left) hfWV
    (pointMap hw₀) cV' hrange
  have hlW : ∀ x : l, ∃ r : cW.ring, (pointValue cW).hom r = algebraMap l L x := by
    intro x
    obtain ⟨r, hr⟩ := hlV x
    refine ⟨ρ.hom r, ?_⟩
    have h1 : cV'.ringMap (pointMap hw₀ ≫ D.B.inclusion.map hWV.left) hrange = pointValue cL :=
      AffineChart.ringMap_congr cL hrange (range_pointMap cL) hptW
    rw [← hr, ← h1, hρ]
    rfl
  obtain ⟨BW, ⟨eW⟩, hBW⟩ := exists_sliceEquivalence_of_isSeparable cW hfinL.1 hfinL.2 hlW
  -- the étale chart step
  obtain ⟨kW, hkW⟩ := exists_oneMorphism_representingMap_eq' D.B D.S D.hS
    (schemeFibredCategory D.B D.S D.hS W) T.pt.val (yoneda.obj W) Q
    (PresheafOfCategories.sliceElementsEquivalenceOver W) eQ a
  let K := CatFiberedInGroupoids.homFunctor kW
  have hK : K ⋙ T.pt.val.val.p = Over.forget W := CatFiberedInGroupoids.homFunctor_comp_p kW
  have hKa : ∀ u : Over W, a.app (op u.left) u.hom =
      PresheafOfCategories.sectionOfObj eQ (K.obj u) (Functor.congr_obj hK u) := by
    intro u
    rw [← hkW]
    exact representingMap_app_hom D.B D.S D.hS T.pt.val Q eQ W kW u
  let r₀ := Deformation.Artin.selfIntersectionPoint D.B D.S D.hS (Over.forget V) D.𝒳.val.val.p
    Φ hΦ uL
  have hr₀ := Deformation.Artin.selfIntersectionPoint_base D.B D.S D.hS (Over.forget V)
    D.𝒳.val.val.p Φ hΦ iΛ uL huL
  have hsec : PresheafOfCategories.sectionOfObj eQ r₀ (rfl : T.pt.val.val.p.obj r₀ = w₀.left) =
      PresheafOfCategories.sectionOfObj eQ (K.obj w₀) (Functor.congr_obj hK w₀) := by
    rw [← hKa]
    have h1 := representingMap_app_hom D.B D.S D.hS T.pt.val Q eQ V δ.hom.hom uL
    have h2 := congrArg (fun t : yoneda.obj w₀.left ⟶ Q => t.app (op w₀.left) (𝟙 w₀.left)) hπa
    simp only [NatTrans.comp_app_apply, yoneda_map_app] at h2
    exact h1.symm.trans h2.symm
  let eψ := PresheafOfCategories.fiberIsoOfSectionOfObj_eq eQ
    (rfl : T.pt.val.val.p.obj r₀ = w₀.left) (Functor.congr_obj hK w₀) hsec
  let r₀' : T.pt.val.val.obj := r₀
  let ψ : r₀' ⟶ K.obj w₀ := eψ.hom.1
  have : IsIso ψ := (Functor.Fiber.fiberInclusion.mapIso eψ).isIso_hom
  have hψ : (T.pt.val.val.p ⋙ Over.post D.B.inclusion).map ψ = eqToHom (hr₀.trans
      ((Deformation.Artin.transport_obj_eq D.B D.hS (Over.forget W) T.pt.val.val.p K hK w₀).trans
        hw₀).symm) := by
    have hL : T.pt.val.val.p.IsHomLift (𝟙 w₀.left) ψ := eψ.hom.2
    have hmap := IsHomLift.fac' T.pt.val.val.p (𝟙 w₀.left) ψ
    show (Over.post D.B.inclusion).map (T.pt.val.val.p.map ψ) = _
    rw [hmap]
    apply Over.OverMorphism.ext
    simp only [eqToHom_map, Over.eqToHom_left, Category.id_comp, eqToHom_trans]
    rfl
  let EW := Deformation.Artin.predeformationEquivalenceOfFormallyEtale iΛ W T.pt.val.val.p Q eQ K
    hK a T.pt.val.property (Space.formallyEtale_of_etale D.B D.S D.hS a ha) hKa w₀ hw₀ r₀ hr₀ ψ hψ
  -- Stacks 07WL at the diagonal point
  let L07 := Deformation.Artin.selfIntersectionPredeformationEquivalence D.B D.S D.hS
    (Over.forget V) D.𝒳.val.val.p Φ hΦ iΛ uL huL (Functor.IsFiberedInGroupoids.over_forget V)
    D.𝒳.val.property (Deformation.Artin.satisfiesRS_over_forget D.B D.S D.hS V) hRS hfinL.1 hfinL.2
  let := (Deformation.Artin.predeformationCategory iΛ
    (T.pt.val.val.p ⋙ Over.post D.B.inclusion) r₀ hr₀).category
  let := (Deformation.Artin.predeformationCategory iΛ
    (Over.forget W ⋙ Over.post D.B.inclusion) w₀ hw₀).category
  let := (Deformation.Artin.predeformationCategory iΛ
    (Over.forget V ⋙ Over.post D.B.inclusion) uL huL).category
  let := (Deformation.Artin.predeformationCategory iΛ
    (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) xL hxL).category
  let eB := (L07.symm.trans EW.symm).trans eW.symm
  have hp := Deformation.Artin.predeformationCategory_isPredeformationCategory
    D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property
  have hpL := Deformation.Artin.predeformationCategory_isPredeformationCategory
    D.B D.hS iΛ D.𝒳.val.val.p xL hxL D.𝒳.val.property
  obtain ⟨a, b, a', b', ha, hb, ha', hb', hab⟩ :=
    Deformation.twoMul_ringKrullDim_sub_eq_of_smoothChart T₀ _ hp ξ hξ Bv e _ hpL E AV BW eV
      mF.toFunctor mF.projection_comm hsm eB
  refine ⟨a, b, a', b', ha, hb, ?_, ?_, hab⟩
  · rw [← hpt, ringKrullDim_stalk_eq_localization cL, ← hAV, ha']
  · rw [ringKrullDim_stalk_eq_localization cW, ← hBW, hb']

/-- The field-valued point of `𝒳` given by an object `x₀` lying over `Spec k ⟶ Spec Λ ⟶ S`. -/
def objectFieldValuedPoint {𝒳 : AlgebraicStacks.{u, w} B S hS} {Λ k : Type u} [CommRing Λ]
    [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S) (x₀ : 𝒳.val.val.obj)
    (hx₀ : (𝒳.val.val.p ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    FieldValuedPoint B S hS 𝒳.val.val where
  carrier := k
  base := 𝒳.val.val.p.obj x₀
  isSpec := eqToIso (congrArg Over.left hx₀)
  obj := x₀
  «over» := rfl

/-- The point `[x₀] ∈ |𝒳|` of an object `x₀` lying over `Spec k ⟶ Spec Λ ⟶ S`. -/
abbrev objectPoint {𝒳 : AlgebraicStacks.{u, w} B S hS} {Λ k : Type u} [CommRing Λ]
    [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S) (x₀ : 𝒳.val.val.obj)
    (hx₀ : (𝒳.val.val.p ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    points B S hS 𝒳.val.val 𝒳.val.property :=
  pointClass B S hS 𝒳.val.val 𝒳.val.property (objectFieldValuedPoint B S hS iΛ x₀ hx₀)

/-- **In Situation 0DQU the algebraic stack is locally Noetherian**: a smooth chart is locally
of finite type over the locally Noetherian base. -/
theorem isLocallyNoetherianStack_of_versalSituation (D : VersalSituation.{u, w}) :
    IsLocallyNoetherianStack.{u, w} D.B D.S D.hS D.𝒳 := by
  obtain ⟨U, f, hf, hsurj⟩ := exists_smooth_surjective_schemeStack.{u, w} D.B D.S D.hS D.𝒳
  have : LocallyOfFiniteType (D.B.inclusion.map U.hom) :=
    locallyOfFiniteType_of_isSmooth_schemeStack D.B D.S D.hS D.𝒳 D.locallyFiniteType U f hf
  have : IsLocallyNoetherian (D.B.inclusion.obj (D.B.obj D.hS)) :=
    inferInstanceAs (IsLocallyNoetherian D.S)
  exact ⟨U, f, hsurj, hf, LocallyOfFiniteType.isLocallyNoetherian (D.B.inclusion.map U.hom)⟩

/-- A field-valued point of a scheme, locally of finite type, whose residue field map is
surjective, lies over a finite type point. -/
theorem isFiniteTypePoint_of_surjective_residueFieldMap {Y : Scheme.{u}} {K : Type u} [Field K]
    (pt : Spec (.of K) ⟶ Y) [LocallyOfFiniteType pt]
    (hres : Function.Surjective (Scheme.SpecToEquivOfField K Y pt).2) :
    _root_.AlgebraicGeometry.IsFiniteTypePoint ((Scheme.SpecToEquivOfField K Y pt).1) := by
  set xf := Scheme.SpecToEquivOfField K Y pt with hxf
  have hfac : pt = Spec.map xf.2 ≫ Y.fromSpecResidueField xf.1 :=
    ((Scheme.SpecToEquivOfField K Y).left_inv pt).symm
  let eR : Y.residueField xf.1 ≃+* K :=
    RingEquiv.ofBijective xf.2.hom ⟨RingHom.injective _, hres⟩
  have : IsIso xf.2 := (RingEquiv.toCommRingCatIso eR).isIso_hom
  have h : Y.fromSpecResidueField xf.1 = inv (Spec.map xf.2) ≫ pt := by
    rw [hfac, IsIso.inv_hom_id_assoc]
  have hl : LocallyOfFiniteType (Y.fromSpecResidueField xf.1) := by rw [h]; infer_instance
  exact ((finiteType_specField_tfae (k := Y.residueField xf.1)
    (Y.fromSpecResidueField xf.1)).out 2 1).mp hl

section ChartPoint

variable {B S hS}

/-- The scheme morphism underlying `eqToHom h ≫ f` is `eqToHom _` composed with that of `f`. -/
theorem toScheme_map_eqToHom_comp {X Y Z : BigFppfOver B S hS} (h : X = Y) (f : Y ⟶ Z) :
    (BigFppfOver.toScheme B S hS).map (eqToHom h ≫ f) =
      eqToHom (by rw [h]) ≫ (BigFppfOver.toScheme B S hS).map f := by
  subst h
  simp

/-- If the scheme morphism underlying `f` is locally of finite type, so is that underlying
`eqToHom h ≫ f`. -/
theorem locallyOfFiniteType_toScheme_map_eqToHom_comp {X Y Z : BigFppfOver B S hS} (h : X = Y)
    (f : Y ⟶ Z) [LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map f)] :
    LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map (eqToHom h ≫ f)) := by
  subst h
  simpa

/-- The field-valued point of the presheaf represented by `V` given by an object `u` of `(Sch/V)`
lying over `Spec L ⟶ Spec Λ ⟶ S`. -/
def chartFieldPoint {V : BigFppfOver B S hS} {Λ L : Type u} [CommRing Λ] [Field L] [Algebra Λ L]
    (iΛ : Spec (.of Λ) ⟶ S) (u : Over V)
    (hu : (Over.forget V ⋙ Over.post B.inclusion).obj u =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ L)) ≫ iΛ)) :
    Space.FieldValuedPoint B S hS (yoneda.obj V) where
  carrier := L
  contained := Deformation.Artin.contains_spec_of_post_eq_site iΛ hu
  toBase := Spec.map (CommRingCat.ofHom (algebraMap Λ L)) ≫ iΛ
  value := eqToHom (Deformation.Artin.post_obj_injective
    (show (Over.post B.inclusion).obj
        (Over.mk (⟨Spec.map (CommRingCat.ofHom (algebraMap Λ L)) ≫ iΛ⟩ :
          B.obj (Deformation.Artin.contains_spec_of_post_eq_site iΛ hu) ⟶ B.obj hS)) =
        (Over.post B.inclusion).obj u.left from hu.symm)) ≫ u.hom

/-- The point of `V` of the field-valued point `chartFieldPoint iΛ u hu` is the image of the closed
point of `Spec L` under `pointMap hu`. -/
theorem schemePoint_chartFieldPoint {V : BigFppfOver B S hS} {Λ L : Type u} [CommRing Λ]
    [Field L] [Algebra Λ L] (iΛ : Spec (.of Λ) ⟶ S) (u : Over V)
    (hu : (Over.forget V ⋙ Over.post B.inclusion).obj u =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ L)) ≫ iΛ)) :
    Space.schemePoint B S hS V (chartFieldPoint iΛ u hu) =
      (pointMap hu).base (closedPt (.of L)) := by
  have hm : (BigFppfOver.toScheme B S hS).map (chartFieldPoint iΛ u hu).value = pointMap hu :=
    (toScheme_map_eqToHom_comp _ u.hom).trans rfl
  show ((BigFppfOver.toScheme B S hS).map (chartFieldPoint iΛ u hu).value).base
    (closedPt (.of L)) = _
  rw [hm]
  rfl

/-- The point of `𝒳` of a chart point `u` with an arrow `g(u) ⟶ x₀` is the point of `x₀`. -/
theorem pointsMap_chartFieldPoint {𝒳 : AlgebraicStacks.{u, w} B S hS} {V : BigFppfOver B S hS}
    (g : schemeStack.{u, w} B S hS V ⟶ 𝒳) {Λ k L : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    [Field L] [Algebra Λ L] (iΛ : Spec (.of Λ) ⟶ S) (x₀ : 𝒳.val.val.obj)
    (hx₀ : (𝒳.val.val.p ⋙ Over.post B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) (u : Over V)
    (hu : (Over.forget V ⋙ Over.post B.inclusion).obj u =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ L)) ≫ iΛ))
    (η : (CatFiberedInGroupoids.homFunctor g.hom).obj u ⟶ x₀) :
    pointsMap B S hS (schemeFibredCategory B S hS V).val (schemeFibredCategory B S hS V).property
        𝒳.val.property g.hom.hom
        (representedChartPointMap B S hS V ((chartFieldPoint iΛ u hu).class B S hS _)) =
      objectPoint B S hS iΛ x₀ hx₀ := by
  rw [representedChartPointMap, spacePointMap_class, pointsMap_class]
  apply (class_eq_class_iff_hasCommonExtension B S hS _ _ _ _).2
  let arr : Over.mk (chartFieldPoint iΛ u hu).value ⟶ u :=
    Over.homMk (eqToHom (Deformation.Artin.post_obj_injective
      (show (Over.post B.inclusion).obj
          (Over.mk (⟨Spec.map (CommRingCat.ofHom (algebraMap Λ L)) ≫ iΛ⟩ :
            B.obj (Deformation.Artin.contains_spec_of_post_eq_site iΛ hu) ⟶ B.obj hS)) =
          (Over.post B.inclusion).obj u.left from hu.symm))) rfl
  exact ⟨_, ⟨𝟙 _⟩, ⟨g.hom.hom.toFunctor.map arr ≫ η⟩⟩

/-- The point of `𝒳` of a chart point of a smooth chart, locally of finite type over `S`, is a
finite type point. -/
theorem isFiniteTypePoint_pointsMap_chartFieldPoint {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {V : BigFppfOver B S hS} [LocallyOfFiniteType (B.inclusion.map V.hom)]
    (g : schemeStack.{u, w} B S hS V ⟶ 𝒳) (hg : AlgebraicStacks.IsSmooth B S hS g)
    {Λ L : Type u} [CommRing Λ] [Field L] [Algebra Λ L] (iΛ : Spec (.of Λ) ⟶ S) (u : Over V)
    (hu : (Over.forget V ⋙ Over.post B.inclusion).obj u =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ L)) ≫ iΛ))
    (hfin : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ L)) ≫ iΛ)) :
    IsFiniteTypePoint.{u, w} B S hS 𝒳
      (pointsMap B S hS (schemeFibredCategory B S hS V).val (schemeFibredCategory B S hS V).property
        𝒳.val.property g.hom.hom
        (representedChartPointMap B S hS V ((chartFieldPoint iΛ u hu).class B S hS _))) := by
  refine mapsTo_finiteTypePoints B S hS g
    (AlgebraicStacks.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
      (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS g hg)) ?_
  rw [representedChartPointMap, spacePointMap_class]
  refine ⟨_, rfl, isLocallyOfFiniteType_fieldValuedPointStackMorphism_schemeStack.{u, w}
    B S hS V _ ?_⟩
  rw [Space.isLocallyOfFiniteType_yoneda_map_iff]
  let pt := (BigFppfOver.toScheme B S hS).map (chartFieldPoint iΛ u hu).value
  have hcomp : pt ≫ B.inclusion.map V.hom =
      Spec.map (CommRingCat.ofHom (algebraMap Λ L)) ≫ iΛ := by
    show B.inclusion.map (chartFieldPoint iΛ u hu).value.left ≫ B.inclusion.map V.hom = _
    rw [← Functor.map_comp, Over.w (chartFieldPoint iΛ u hu).value]
    rfl
  have : LocallyOfFiniteType (pt ≫ B.inclusion.map V.hom) := by
    rw [hcomp]
    exact hfin
  have : LocallyOfFiniteType pt := locallyOfFiniteType_of_comp pt (B.inclusion.map V.hom)
  exact locallyOfFiniteType_toScheme_map_eqToHom_comp _ (chartFieldPoint iΛ u hu).value

end ChartPoint

/-- **The point of an object of finite type of an algebraic stack in Situation 0DQU is a finite
type point.** A smooth chart point over it
(`AlgebraicGeometry.Stack.exists_smoothChart_point_residueField_eq`) maps to it, and its image is
a finite type point by Stacks 06G0. -/
theorem isFiniteTypePoint_objectPoint (D : VersalSituation.{u, w})
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    IsFiniteTypePoint.{u, w} D.B D.S D.hS D.𝒳 (objectPoint D.B D.S D.hS iΛ x₀ hx₀) := by
  obtain ⟨l, _, _, _, _, hkl, -, V, g, hg, hV, u₀, hu₀, -, η, -⟩ :=
    exists_smoothChart_point_residueField_eq D iΛ hiΛ x₀ hx₀ hfinite
  have := hV
  have hfinl := Deformation.Artin.locallyOfFiniteType_quasiCompact_of_finite (k := k) (l := l)
    iΛ hfinite
  rw [← pointsMap_chartFieldPoint g iΛ x₀ hx₀ u₀ hu₀ η]
  exact isFiniteTypePoint_pointsMap_chartFieldPoint g hg iΛ u₀ hu₀ hfinl.1

/-- **Stacks 0DSB, for any ring prorepresenting the isomorphisms of a versal object.** In Situation
0DQU, let `x₀` be an object of `𝒳` over `Spec k`, `k` of finite type over `S`, let `Spec Λ ⊆ S` be
an affine open through which `Spec k ⟶ S` factors with `Λ → k` finite (Section 07T2), let `ξ` be a
versal formal object of `𝓕_{𝒳,k,x₀}` over `A` and let `B` be a Noetherian complete local
`Λ`-algebra with residue field `k` with `B|_{𝒞_Λ} ≅ A|_{𝒞_Λ} ×_{ξ, 𝓕, ξ} A|_{𝒞_Λ}`. Then the
dimension of the local ring of `𝒳` at the point of `x₀` (Stacks 0DSA) is `2 dim A - dim B`. -/
theorem hasLocalRingDimension_of_isVersal (D : VersalSituation.{u, w})
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    let C := Deformation.Artin.predeformationCategory iΛ
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀
    letI := C.category
    let hp := Deformation.Artin.predeformationCategory_isPredeformationCategory
      D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property
    ∀ (ξ : Deformation.FormalObject C.projection) (_ : Deformation.IsVersal hp.cofibered ξ)
      (Bv : Deformation.CompleteLocalAlgCat.{u, u, u} Λ k)
      (_ : Deformation.restrictedCoyoneda Bv ≅
        (Deformation.versalGroupoid C.projection hp ξ).arrows),
      ∃ m n : ℕ, ringKrullDim ξ.base = m ∧ ringKrullDim Bv = n ∧
        HasLocalRingDimensionAtSomeChart D.B D.S D.hS D.𝒳
          (isLocallyNoetherianStack_of_versalSituation D)
          (objectPoint D.B D.S D.hS iΛ x₀ hx₀)
          (isFiniteTypePoint_objectPoint D iΛ hiΛ x₀ hx₀ hfinite) (2 * (m : ℤ) - (n : ℤ)) := by
  intro C hp ξ hξ Bv e
  have : _root_.AlgebraicGeometry.IsOpenImmersion iΛ := hiΛ
  obtain ⟨l, _, _, _, _, hkl, hsep, V, g, hg, hV, u₀, hu₀, hxₗ, η, hη, -, hc₀, hres⟩ :=
    exists_smoothChart_point_residueField_eq D iΛ hiΛ x₀ hx₀ hfinite
  have := hV
  have hfinl := Deformation.Artin.locallyOfFiniteType_quasiCompact_of_finite (k := k) (l := l)
    iΛ hfinite
  let T := twoFibreProductSquareAlgebraicStacks D.B D.S D.hS g g
  have hT := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks D.B D.S D.hS g g
  have hrep : IsRepresentableByAlgebraicSpaces D.B D.S D.hS g.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack D.B D.S D.hS D.𝒳.property
      (isRepresentableByAlgebraicSpace_schemeFibredCategory D.B D.S D.hS V) _
  obtain ⟨Q, hQ, ⟨eQ⟩⟩ := isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u}
    D.B D.S D.hS (schemeFibredCategory D.B D.S D.hS V) D.𝒳.val (schemeFibredCategory D.B D.S D.hS V)
    g.hom g.hom (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom g.hom)
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      g.hom g.hom) hrep (isRepresentableByAlgebraicSpace_schemeFibredCategory D.B D.S D.hS V)
  let eQ' : StacksRepresentableCFG.EquivalenceOver T.pt.val.val.p
      (presheafOfCategories (Q ⋙ typeToCat)).p := eQ
  let eV₀ := PresheafOfCategories.sliceElementsEquivalenceOver V
  let δ := selfIntersectionDiagonalPreHom D.B D.S D.hS V g
  obtain ⟨W, a, -, ha, L, _, _, _, _, hlL, hsepL, w₀, hw₀, π, hπ, hπa, -⟩ :=
    exists_etaleChart_point_isSeparable_selfIntersection D.B D.S D.hS V g T Q hQ eV₀ eQ' δ
      u₀ hu₀ hres
  -- the étale chart is locally of finite type over `S`
  let sQ := selfIntersectionSourceMap D.B D.S D.hS V g T Q eV₀ eQ'
  have hsQ : Space.IsSmooth D.B D.S D.hS sQ :=
    isSmooth_selfIntersectionSourceMap D.B D.S D.hS V g T Q eV₀ eQ' hg hT hQ
  have hWlft : Space.IsLocallyOfFiniteType D.B D.S D.hS (a ≫ sQ) :=
    Space.isLocallyOfFiniteType_comp' D.B D.S D.hS a sQ hQ (isAlgebraicSpace_yoneda D.B D.S D.hS V)
      (Space.isLocallyOfFiniteType_of_isEtale' D.B D.S D.hS a
        ((Space.isEtale_iff_presheaf_of_yoneda D.B D.S D.hS a).mpr ha))
      (Space.isLocallyOfFiniteType_of_isSmooth D.B D.S D.hS hsQ)
  let hWV : W ⟶ V := yoneda.preimage (a ≫ sQ)
  have : LocallyOfFiniteType ((BigFppfOver.toScheme D.B D.S D.hS).map hWV) := by
    rw [← Space.isLocallyOfFiniteType_yoneda_map_iff, Functor.map_preimage]
    exact hWlft
  have : LocallyOfFiniteType (D.B.inclusion.map W.hom) := by
    have hw : D.B.inclusion.map W.hom =
        (BigFppfOver.toScheme D.B D.S D.hS).map hWV ≫ D.B.inclusion.map V.hom := by
      rw [← Over.w hWV, Functor.map_comp]
      rfl
    rw [hw]
    infer_instance
  obtain ⟨a₁, b₁, a₂, b₂, h1, h2, h3, h4, h5⟩ := twoMul_ringKrullDim_eq_of_chartPoints D iΛ x₀ hx₀
    hfinite ξ hξ Bv e V g hg u₀ hu₀ hxₗ η hη hc₀ Q eQ' W a ha w₀ hw₀ π hπ hπa
  -- the points
  let uL : Over V := Over.mk (π ≫ u₀.hom)
  have huL : (Over.forget V ⋙ Over.post D.B.inclusion).obj uL =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ L)) ≫ iΛ) := hw₀
  let pν := chartFieldPoint iΛ uL huL
  let pw := chartFieldPoint iΛ w₀ hw₀
  let eδ := selfIntersectionDiagonalMap D.B D.S D.hS V g T Q eV₀ eQ' δ
  have hes : eδ ≫ sQ = 𝟙 _ := selfIntersectionDiagonalMap_comp_sourceMap D.B D.S D.hS V g T Q
    eV₀ eQ' δ
  obtain ⟨hptL, hpt⟩ := pointMap_comp_algebraMap_eq D.B D.S D.hS π hu₀ hw₀ huL hπ
  let ηL := (CatFiberedInGroupoids.homFunctor g.hom).map (Over.homMk π rfl : uL ⟶ u₀) ≫ η
  refine ⟨a₁, b₁, h1, h2, V, g, T, hT, Q, hQ, eQ', δ, pν.class D.B D.S D.hS _, hg, ?_,
    pointsMap_chartFieldPoint g iΛ x₀ hx₀ uL huL ηL, ?_⟩
  · rw [Space.pointsToScheme_class, schemePoint_chartFieldPoint, hpt]
    have hcomp : pointMap hu₀ ≫ D.B.inclusion.map V.hom =
        Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ := pointMap_comp
    have : LocallyOfFiniteType (pointMap hu₀ ≫ D.B.inclusion.map V.hom) := by
      rw [hcomp]
      exact hfinl.1
    have : LocallyOfFiniteType (pointMap hu₀) :=
      locallyOfFiniteType_of_comp (pointMap hu₀) (D.B.inclusion.map V.hom)
    exact isFiniteTypePoint_of_surjective_residueFieldMap (pointMap hu₀) hres
  · refine ⟨a₂, b₂, ?_, ?_, ?_⟩
    · have hid : Space.pointsMap D.B D.S D.hS Q sQ
          (Space.pointsMap D.B D.S D.hS (yoneda.obj V) eδ (pν.class D.B D.S D.hS _)) =
            pν.class D.B D.S D.hS _ := by
        rw [← Function.comp_apply (f := Space.pointsMap D.B D.S D.hS Q sQ),
          ← Space.pointsMap_comp, hes, Space.pointsMap_id]
        rfl
      show Space.localRingDimension D.B D.S D.hS (Space.pointsMap D.B D.S D.hS Q sQ
          (Space.pointsMap D.B D.S D.hS (yoneda.obj V) eδ (pν.class D.B D.S D.hS _))) = _
      rw [hid]
      have hch := Space.localRingDimension_eq_of_chartPoint D.B D.S D.hS
        (isAlgebraicSpace_yoneda D.B D.S D.hS V) V (𝟙 _)
        ((Space.isEtale_iff_presheaf_of_yoneda D.B D.S D.hS (𝟙 _)).mp
          (Space.isEtale_of_isIso D.B D.S D.hS _))
        (Space.schemePoint D.B D.S D.hS V pν) (pν.class D.B D.S D.hS _)
        ⟨pν, rfl, by rw [Space.pointsMap_id]; rfl⟩
      rw [schemePoint_chartFieldPoint, hpt] at hch
      change (Space.localRingDimension D.B D.S D.hS (pν.class D.B D.S D.hS _) : WithBot ℕ∞) =
        ringKrullDim ((D.B.inclusion.obj V.left).presheaf.stalk
          ((pointMap hu₀).base (closedPt (.of l)))) at hch
      rw [h3] at hch
      exact_mod_cast hch
    · have hmatch : Space.pointsMap D.B D.S D.hS (yoneda.obj W) a (pw.class D.B D.S D.hS _) =
          Space.pointsMap D.B D.S D.hS (yoneda.obj V) eδ (pν.class D.B D.S D.hS _) := by
        rw [Space.pointsMap_class, Space.pointsMap_class]
        congr 1
        have h := congrArg (fun t : yoneda.obj w₀.left ⟶ Q =>
          t.app (op pw.siteObject) (eqToHom (Deformation.Artin.post_obj_injective
            (show (Over.post D.B.inclusion).obj pw.siteObject =
              (Over.post D.B.inclusion).obj w₀.left from hw₀.symm)))) hπa
        simp only [NatTrans.comp_app_apply, yoneda_map_app] at h
        simp only [Space.FieldValuedPoint.map]
        congr 1
      have hch := Space.localRingDimension_eq_of_chartPoint D.B D.S D.hS hQ W a ha
        (Space.schemePoint D.B D.S D.hS W pw)
        (Space.pointsMap D.B D.S D.hS (yoneda.obj V) eδ (pν.class D.B D.S D.hS _))
        ⟨pw, rfl, hmatch⟩
      rw [schemePoint_chartFieldPoint] at hch
      change (Space.localRingDimension D.B D.S D.hS (Space.pointsMap D.B D.S D.hS (yoneda.obj V) eδ
          (pν.class D.B D.S D.hS _)) : WithBot ℕ∞) =
        ringKrullDim ((D.B.inclusion.obj W.left).presheaf.stalk
          ((pointMap hw₀).base (closedPt (.of L)))) at hch
      rw [h4] at hch
      exact_mod_cast hch
    · omega

/-- **Stacks 0DSB.** Let `𝒳` be an algebraic stack, locally of finite type over a locally
Noetherian scheme `S` (Situation 0DQU), and let `x₀ : Spec k ⟶ 𝒳` be a morphism, `k` a field of
finite type over `S`, with `Spec Λ ⊆ S` an affine open through which `Spec k ⟶ S` factors with
`Λ → k` finite (Section 07T2). Represent `𝓕_{𝒳,k,x₀}` as in Remark 0DR3 by a cogroupoid
`(A, B, s, t, c)` of Noetherian complete local `Λ`-algebras with residue field `k`: a versal formal
object `ξ` over `A` and a representable presentation `P` on `𝒞^_Λ` with objects `P.objects = A`,
arrows `P.arrows = B`, source and target `s = P.source`, `t = P.target` and comultiplication
`c = P.comultiplication`, whose restriction to `𝒞_Λ` is the groupoid in functors
`(A|_{𝒞_Λ}, A|_{𝒞_Λ} ×_{ξ, 𝓕, ξ} A|_{𝒞_Λ})` of `ξ` (this is the representation produced by
`AlgebraicGeometry.Stack.exists_versalCogroupoid_predeformationCategory`). Then the dimension of
the local ring of `𝒳` at the point of `x₀` (Stacks 0DSA) is `2 dim A - dim B`.

Every such representation is allowed, so the statement holds for all of them; the two dimensions
are finite and are recorded as natural numbers before the difference is taken, as in Stacks
0DSA. -/
@[stacks 0DSB]
theorem hasLocalRingDimension_of_versalCogroupoid (D : VersalSituation.{u, w})
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    let C := Deformation.Artin.predeformationCategory iΛ
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀
    letI := C.category
    let hp := Deformation.Artin.predeformationCategory_isPredeformationCategory
      D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property
    ∀ (ξ : Deformation.FormalObject C.projection) (_ : Deformation.IsVersal hp.cofibered ξ)
      (P : Deformation.RepresentablePresentation.{_, u, u}
        (Deformation.CompleteLocalAlgCat.{u, u, u} Λ k)),
      P.objects = ξ.base →
      Nonempty (Deformation.versalGroupoid C.projection hp ξ ≅
        Deformation.GroupoidInFunctors.restrict P.groupoidInFunctors
          Deformation.artinianToComplete) →
      ∃ m n : ℕ, ringKrullDim P.objects = m ∧ ringKrullDim P.arrows = n ∧
        HasLocalRingDimensionAtSomeChart D.B D.S D.hS D.𝒳
          (isLocallyNoetherianStack_of_versalSituation D)
          (objectPoint D.B D.S D.hS iΛ x₀ hx₀)
          (isFiniteTypePoint_objectPoint D iΛ hiΛ x₀ hx₀ hfinite) (2 * (m : ℤ) - (n : ℤ)) := by
  intro C hp ξ hξ P hPo ⟨eG⟩
  let K := Deformation.GroupoidInFunctors.restrict P.groupoidInFunctors
    Deformation.artinianToComplete
  -- the arrow functors of an isomorphism of groupoids in functors
  let eA : (Deformation.versalGroupoid C.projection hp ξ).arrows ≅ K.arrows :=
    { hom := eG.hom.mapArrows
      inv := eG.inv.mapArrows
      hom_inv_id := congrArg (fun f : Deformation.GroupoidInFunctors.Hom _ _ => f.mapArrows)
        eG.hom_inv_id
      inv_hom_id := congrArg (fun f : Deformation.GroupoidInFunctors.Hom _ _ => f.mapArrows)
        eG.inv_hom_id }
  let uB : K.arrows ≅ Deformation.restrictedCoyoneda P.arrows :=
    Functor.isoWhiskerLeft Deformation.artinianToComplete
      ((CategoryTheory.uliftCoyonedaIsoCoyoneda.{u}).app (op P.arrows))
  obtain ⟨m, n, hm, hn, h⟩ := hasLocalRingDimension_of_isVersal D iΛ hiΛ x₀ hx₀ hfinite ξ hξ
    P.arrows (uB.symm ≪≫ eA.symm)
  exact ⟨m, n, hPo ▸ hm, hn, h⟩

end AlgebraicGeometry.Stack

end
