module

public import StacksFrontier.AlgebraicGeometry.Stacks.LocalRingDimensionVersal
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalRingDimensionChartComparison

/-!
# MathGraph contract witness for Stacks 0DSB

This deliberate *type-level* regression test only elaborates when the theorem tagged
0DSB concludes the canonical chart-independent relation, rather than the legacy
existentially-quantified presentation relation.

It is not a proof that the legacy definition admits two integers. That requires a
separate native geometric counterexample, and must not be inferred from this file.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w

/-- The *actual downstream consumer* demands Stacks 0DSB's chart-independent value. -/
theorem mathGraph_0DSB_canonical_contract (D : VersalSituation.{u, w})
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
          (isFiniteTypePoint_objectPoint D iΛ hiΛ x₀ hx₀ hfinite)
          (2 * (m : ℤ) - (n : ℤ)) := by
  exact hasLocalRingDimension_of_versalCogroupoid D iΛ hiΛ x₀ hx₀ hfinite

end AlgebraicGeometry.Stack

end
