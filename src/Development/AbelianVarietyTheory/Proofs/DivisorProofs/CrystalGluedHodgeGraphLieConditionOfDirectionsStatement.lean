module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArtinianRingTsze
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CanonicalOfAbelianDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RedPullConstMorVPull
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentsMemOfSumMemDistinctEigencharactersModStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrysActApply
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberHodgeSummandEqGraphCoordinates

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.HTGlueLie
variable {k : Type} [Field k] {A₀ : Over (Sp k)} [GrpObj A₀]

theorem inr_one_mul (y : TrivSqZeroExt k k) :
    (TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) * y = TrivSqZeroExt.inr y.fst := by
  ext
  · simp
  · simp

theorem fstC_inr_smul (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀) :
    fstC A₀ ((TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) • e) = 0 := by
  ext c
  rw [fstC_apply]
  change ((TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) * e ((GlobalTheory.FODef.constMorV k k A₀).pull c)).fst = 0
  rw [inr_one_mul, TrivSqZeroExt.fst_inr]

theorem sndC_inr_smul (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀) :
    (sndC A₀ ((TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) • e) : HdR A₀) = fstC A₀ e := by
  ext c
  change (sndC A₀ _) c = fstC A₀ e c
  rw [sndC_apply, fstC_apply]
  change ((TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) * e ((GlobalTheory.FODef.constMorV k k A₀).pull c)).snd = _
  rw [inr_one_mul, TrivSqZeroExt.snd_inr]

theorem exists_of_coords_self (hA : IsAbelianScheme A₀) (x : HdR A₀) (y : primDR A₀ →ₗ[k] k) :
    ∃ e : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀, fstC A₀ e = x ∧ sndC A₀ e = y :=
  exists_of_coords hA x y

theorem ext_coords_self (hA : IsAbelianScheme A₀) {e e' : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀}
    (h1 : fstC A₀ e = fstC A₀ e') (h2 : (sndC A₀ e : HdR A₀) = sndC A₀ e') : e = e' :=
  ext_coords hA h1 h2



theorem dualNumber_hodge_summand_eq_graph_coords_of_compl (hA : IsAbelianScheme A₀) (f : HdR A₀ →ₗ[k] HdR A₀)
    (E M : Submodule (TrivSqZeroExt k k)
      (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀))
    (hEM : IsCompl E M)
    (h2 : ∀ y : HdR A₀, y ∈ Fil A₀ ↔ ∃ e ∈ E,
      (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k k)) rfl A₀).Corr e y)
    (h3 : ∀ x ∈ Fil A₀, ∃ e ∈ E, ∀ c, e ((GlobalTheory.FODef.constMorV k k A₀).pull c) =
      TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (f x c))
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀) :
    e ∈ E ↔ (fstC A₀ e ∈ Fil A₀ ∧ (sndC A₀ e : HdR A₀) - f (fstC A₀ e) ∈ Fil A₀) := by
  have hε := fun e' ↦ And.intro (fstC_inr_smul (A₀ := A₀) e') (sndC_inr_smul (A₀ := A₀) e')
  have hc : ∀ x ∈ Fil A₀, ∃ e ∈ E, fstC A₀ e = x ∧ (sndC A₀ e : HdR A₀) = f x := by
    intro x hx
    refine (h3 x hx).elim fun e₁ hh ↦ ⟨e₁, hh.1, ?_, ?_⟩
    · ext c; rw [fstC_apply, hh.2 c, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
    · ext c; show (sndC A₀ e₁) c = _; rw [sndC_apply, hh.2 c, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
  have hfil : ∀ a ∈ E, fstC A₀ a ∈ Fil A₀ := fun a ha ↦ (h2 _).2 ⟨a, ha, (corr_iff_fstC hA a _).2 rfl⟩
  constructor
  · intro he
    have hx := hfil e he
    obtain ⟨e₁, he₁, h1, h1'⟩ := hc _ hx
    refine ⟨hx, ?_⟩
    have hh := exists_of_coords_self hA ((sndC A₀ e : HdR A₀) - f (fstC A₀ e)) 0
    obtain ⟨yh, hy1, -⟩ := hh
    have hεy : (TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) • yh = e - e₁ := by
      refine ext_coords_self hA ?_ ?_
      · rw [(hε yh).1, map_sub, h1, sub_self]
      · have h5 := (hε yh).2
        rw [hy1] at h5
        show (sndC A₀ _ : HdR A₀) = sndC A₀ (e - e₁)
        rw [h5, map_sub]
        show _ = (sndC A₀ e : HdR A₀) - (sndC A₀ e₁ : HdR A₀)
        rw [h1']
    have hmem : (TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) • yh ∈ E := hεy ▸ E.sub_mem he he₁
    have hyt : yh ∈ E ⊔ M := hEM.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨a, ha, m, hm, hsum⟩ := Submodule.mem_sup.1 hyt
    have hεm : (TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) • m ∈ E := by
      have := E.sub_mem hmem (E.smul_mem (TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) ha)
      rwa [← hsum, smul_add, add_sub_cancel_left] at this
    have hm0 : (TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) • m = 0 :=
      (Submodule.disjoint_def.1 hEM.disjoint) _ hεm (M.smul_mem _ hm)
    have hm1 : fstC A₀ m = 0 := by rw [← (hε m).2, hm0, map_zero]
    rw [← hy1, ← hsum, map_add (f := _), hm1, add_zero]
    exact hfil a ha
  · rintro ⟨hx, hz⟩
    obtain ⟨e₁, he₁, h1, h1'⟩ := hc _ hx
    obtain ⟨e₂, he₂, h2a, -⟩ := hc _ hz
    have : e = e₁ + (TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) • e₂ := by
      refine ext_coords_self hA ?_ ?_
      · rw [map_add (f := _), (hε e₂).1, h1, add_zero]
      · show (sndC A₀ e : HdR A₀) = (sndC A₀ (e₁ + _) : HdR A₀)
        rw [map_add (f := _)]
        show _ = (sndC A₀ e₁ : HdR A₀) + (sndC A₀ (_ • e₂) : HdR A₀)
        rw [(hε e₂).2, h1', h2a, add_sub_cancel]
    rw [this]
    exact E.add_mem he₁ (E.smul_mem _ he₂)

theorem fo_summand_coords : ∀ (k : Type) [Field k] (A₀ : Over (Sp k)) [GrpObj A₀], IsAbelianScheme A₀ → ∀ (f : HdR A₀ →ₗ[k] HdR A₀) (E : Submodule (TrivSqZeroExt k k) (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀)), (∃ M : Submodule (TrivSqZeroExt k k) (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀), IsCompl E M) → (∀ y : HdR A₀, y ∈ Fil A₀ ↔ ∃ e ∈ E, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k k)) rfl A₀).Corr e y) → (∀ x ∈ Fil A₀, ∃ e ∈ E, ∀ c, e ((GlobalTheory.FODef.constMorV k k A₀).pull c) = TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (f x c)) → ∀ e : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀, e ∈ E ↔ (GlobalTheory.HTGlueLie.fstC A₀ e ∈ Fil A₀ ∧ (GlobalTheory.HTGlueLie.sndC A₀ e : HdR A₀) - f (GlobalTheory.HTGlueLie.fstC A₀ e) ∈ Fil A₀) := fun _ _ _ _ hA f E ⟨M, hEM⟩ h2 h3 e ↦
  dualNumber_hodge_summand_eq_graph_coords_of_compl hA f E M hEM h2 h3 e

end GlobalTheory.HTGlueLie
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberHodgeSummandEqGraphCoordinatesStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.dualNumber_hodge_summand_eq_graph_coordinates : ∀ (k : Type) [Field k] (A₀ : Over (Sp k)) [GrpObj A₀], IsAbelianScheme A₀ → ∀ (f : HdR A₀ →ₗ[k] HdR A₀) (E : Submodule (TrivSqZeroExt k k) (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀)), (∃ M : Submodule (TrivSqZeroExt k k) (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀), IsCompl E M) → (∀ y : HdR A₀, y ∈ Fil A₀ ↔ ∃ e ∈ E, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k k)) rfl A₀).Corr e y) → (∀ x ∈ Fil A₀, ∃ e ∈ E, ∀ c, e ((GlobalTheory.FODef.constMorV k k A₀).pull c) = TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (f x c)) → ∀ e : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀, e ∈ E ↔ (GlobalTheory.HTGlueLie.fstC A₀ e ∈ Fil A₀ ∧ (GlobalTheory.HTGlueLie.sndC A₀ e : HdR A₀) - f (GlobalTheory.HTGlueLie.fstC A₀ e) ∈ Fil A₀) := by
  first | (exact @GlobalTheory.HTGlueLie.fo_summand_coords) | (exact GlobalTheory.HTGlueLie.fo_summand_coords) | (intros; apply GlobalTheory.HTGlueLie.fo_summand_coords  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushSubMemGlueFilIff

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTGlueLie

section Coords

variable {k : Type} [Field k] {A₀ : Over (Sp k)} [GrpObj A₀]

theorem fstC_push_sub {V : Type} [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V]
    (g : A₀ ⟶ A₀) [IsMonHom g] (r : k)
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀) :
    fstC A₀ (push (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) g e -
      algebraMap k (TrivSqZeroExt k V) r • e) = push (dp0 k) (𝟙 _) g (fstC A₀ e) - r • fstC A₀ e := by
  rw [map_sub, fstC_push, fstC_smul]

theorem sndC_push_sub {V : Type} [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V]
    (g : A₀ ⟶ A₀) [IsMonHom g] (r : k)
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀) :
    sndC A₀ (push (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) g e -
      algebraMap k (TrivSqZeroExt k V) r • e) = sndC A₀ e ∘ₗ primPull (dp0 k) (𝟙 _) g - r • sndC A₀ e := by
  rw [map_sub, sndC_push, sndC_smul]

theorem proj_comp_sub {d : ℕ} {M : Type*} [AddCommGroup M] [Module k M] (a : M →ₗ[k] (Fin d → k))
    (P : M →ₗ[k] M) (r : k) (j : Fin d) :
    LinearMap.proj j ∘ₗ (a ∘ₗ P - r • a) = (LinearMap.proj j ∘ₗ a) ∘ₗ P - r • (LinearMap.proj j ∘ₗ a) := by
  ext; simp



theorem push_sub_mem_glueFil_iff {d : ℕ} (f : Fin d → (HdR A₀ →ₗ[k] HdR A₀)) (g : A₀ ⟶ A₀) [IsMonHom g] (r : k)
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀) :
    push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) g e -
        algebraMap k (TrivSqZeroExt k (Fin d → k)) r • e ∈ GlobalTheory.HTGlue.glueFil A₀ f ↔
      push (dp0 k) (𝟙 _) g (fstC A₀ e) - r • fstC A₀ e ∈ Fil A₀ ∧
      ∀ j, push (dp0 k) (𝟙 _) g (LinearMap.proj j ∘ₗ sndC A₀ e) - r • (LinearMap.proj j ∘ₗ sndC A₀ e) -
        f j (push (dp0 k) (𝟙 _) g (fstC A₀ e) - r • fstC A₀ e) ∈ Fil A₀ := by
  rw [mem_glueFil_iff, fstC_push_sub]
  refine and_congr Iff.rfl (forall_congr' fun j ↦ ?_)
  have h0 := sndC_push_sub (V := Fin d → k) g r e
  rw [h0, proj_comp_sub]
  rfl



theorem sub_sum_mem_glueFil_iff {d a : ℕ} (f : Fin d → (HdR A₀ →ₗ[k] HdR A₀))
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀)
    (w : Fin a → Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k)))
      (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀) :
    e - ∑ i, w i ∈ GlobalTheory.HTGlue.glueFil A₀ f ↔
      fstC A₀ e - ∑ i, fstC A₀ (w i) ∈ Fil A₀ ∧
      ∀ j, (LinearMap.proj j ∘ₗ sndC A₀ e - ∑ i, LinearMap.proj j ∘ₗ sndC A₀ (w i)) -
        f j (fstC A₀ e - ∑ i, fstC A₀ (w i)) ∈ Fil A₀ := by

  rw [mem_glueFil_iff, map_sub, map_sum]
  refine and_congr Iff.rfl (forall_congr' fun j ↦ ?_)
  have hs : ∀ h : Fin a → (primDR A₀ →ₗ[k] (Fin d → k)),
      LinearMap.proj j ∘ₗ ∑ x, h x = ∑ x, LinearMap.proj j ∘ₗ h x := fun h ↦ by
    ext c; simp [LinearMap.sum_apply]

  rw [map_sub, map_sum, LinearMap.comp_sub, hs]

variable (f : HdR A₀ →ₗ[k] HdR A₀)
  (E : Submodule (TrivSqZeroExt k k) (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀))
  (hE : ∀ e, e ∈ E ↔ (fstC A₀ e ∈ Fil A₀ ∧ (sndC A₀ e : HdR A₀) - f (fstC A₀ e) ∈ Fil A₀))
include hE


theorem push_sub_mem_iff (g : A₀ ⟶ A₀) [IsMonHom g] (r : k)
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀) :
    push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) g e -
        algebraMap k (TrivSqZeroExt k k) r • e ∈ E ↔
      push (dp0 k) (𝟙 _) g (fstC A₀ e) - r • fstC A₀ e ∈ Fil A₀ ∧
      push (dp0 k) (𝟙 _) g (sndC A₀ e) - r • (sndC A₀ e : HdR A₀) -
        f (push (dp0 k) (𝟙 _) g (fstC A₀ e) - r • fstC A₀ e) ∈ Fil A₀ := by
  rw [hE, fstC_push_sub, sndC_push_sub]
  rfl


theorem push_mem_iff (g : A₀ ⟶ A₀) [IsMonHom g]
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀) :
    push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) g e ∈ E ↔
      push (dp0 k) (𝟙 _) g (fstC A₀ e) ∈ Fil A₀ ∧
      push (dp0 k) (𝟙 _) g (sndC A₀ e) - f (push (dp0 k) (𝟙 _) g (fstC A₀ e)) ∈ Fil A₀ := by
  rw [hE, fstC_push, sndC_push]
  rfl


theorem sub_sum_mem_iff {a : ℕ}
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀)
    (w : Fin a → Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀) :
    e - ∑ i, w i ∈ E ↔ fstC A₀ e - ∑ i, fstC A₀ (w i) ∈ Fil A₀ ∧
      ((sndC A₀ e : HdR A₀) - ∑ i, (sndC A₀ (w i) : HdR A₀)) - f (fstC A₀ e - ∑ i, fstC A₀ (w i)) ∈ Fil A₀ := by

  rw [hE, map_sub, map_sub, map_sum, map_sum]

omit hE

end Coords

end GlobalTheory.HTGlueLie
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphLieConditionOfDirections

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTGlueLie

section Core

variable {k : Type} [Field k] {A₀ : Over (Sp k)} [GrpObj A₀]



theorem core (hA : IsAbelianScheme A₀) {O : Type} [CommRing O] (act : O → (A₀ ⟶ A₀)) [∀ c, IsMonHom (act c)]
    (ρ' : O →+* Module.End k (HdR A₀)) (hρ' : ∀ c h, ρ' c h = push (dp0 k) (𝟙 _) (act c) h)
    (ω : O) (r : k) {a : ℕ} (χ : Fin a → O → k) (hχ : ∀ i i', i ≠ i' → ∃ c, χ i c ≠ χ i' c)
    {d : ℕ} (hd : 0 < d) (f : Fin d → (HdR A₀ →ₗ[k] HdR A₀))
    (E' : Fin d → Submodule (TrivSqZeroExt k k)
      (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀))
    (hE : ∀ j e, e ∈ E' j ↔ (fstC A₀ e ∈ Fil A₀ ∧ (sndC A₀ e : HdR A₀) - f j (fstC A₀ e) ∈ Fil A₀))
    (hlift : ∀ j, ∀ x ∈ Fil A₀, ∃ e ∈ E' j, fstC A₀ e = x ∧ (sndC A₀ e : HdR A₀) = f j x)
    (hstab : ∀ j c, ∀ e ∈ E' j,
      push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (act c) e ∈ E' j)
    (hlie : ∀ j e, push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (act ω) e -
        algebraMap k (TrivSqZeroExt k k) r • e ∈ E' j →
      ∃ w : Fin a → Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀,
        (∀ i c, push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (act c) (w i) -
          algebraMap k (TrivSqZeroExt k k) (χ i c) • w i ∈ E' j) ∧ e - ∑ i, w i ∈ E' j)
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀)
    (he : push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom)
        (act ω) e - algebraMap k (TrivSqZeroExt k (Fin d → k)) r • e ∈ GlobalTheory.HTGlue.glueFil A₀ f) :
    ∃ w : Fin a → Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k)))
        (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀,
      (∀ i c, push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom)
          (act c) (w i) - algebraMap k (TrivSqZeroExt k (Fin d → k)) (χ i c) • w i ∈ GlobalTheory.HTGlue.glueFil A₀ f) ∧
        e - ∑ i, w i ∈ GlobalTheory.HTGlue.glueFil A₀ f := by
  rw [push_sub_mem_glueFil_iff] at he
  obtain ⟨he1, he2⟩ := he

  choose ee hee1 hee2 using fun j : Fin d ↦ exists_of_coords (V := k) hA (fstC A₀ e)
    (LinearMap.proj j ∘ₗ sndC A₀ e)
  have hEj : ∀ j, push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (act ω) (ee j) -
      algebraMap k (TrivSqZeroExt k k) r • ee j ∈ E' j := fun j ↦ by
    rw [push_sub_mem_iff (f j) (E' j) (hE j), hee1, hee2]
    exact ⟨he1, he2 j⟩
  choose W hW1 hW2 using fun j ↦ hlie j (ee j) (hEj j)
  have hα := fun j i c ↦ (push_sub_mem_iff (f j) (E' j) (hE j) _ _ _).1 (hW1 j i c)
  have hs : ∀ j, fstC A₀ e - ∑ i, fstC A₀ (W j i) ∈ Fil A₀ ∧
      ((LinearMap.proj j ∘ₗ sndC A₀ e : HdR A₀) - ∑ i, (sndC A₀ (W j i) : HdR A₀)) -
        f j (fstC A₀ e - ∑ i, fstC A₀ (W j i)) ∈ Fil A₀ := fun j ↦ by
    have := (sub_sum_mem_iff (f j) (E' j) (hE j) _ _).1 (hW2 j)
    rwa [hee1, hee2] at this

  have hfstab : ∀ j c, ∀ x ∈ Fil A₀,
      push (dp0 k) (𝟙 _) (act c) (f j x) - f j (push (dp0 k) (𝟙 _) (act c) x) ∈ Fil A₀ := by
    intro j c x hx
    obtain ⟨e1, he1E, h1, h2⟩ := hlift j x hx
    have := ((push_mem_iff (f j) (E' j) (hE j) (act c) e1).1 (hstab j c e1 he1E)).2
    rwa [h1, h2] at this

  let j₀ : Fin d := ⟨0, hd⟩
  have hFst : ∀ c, ∀ x ∈ Fil A₀, ρ' c x ∈ Fil A₀ := fun c x hx ↦ by rw [hρ']; exact push_mem_Fil _ hx
  have hglue : ∀ j i, fstC A₀ (W j i) - fstC A₀ (W j₀ i) ∈ Fil A₀ := fun j ↦
    GlobalTheory.T.components_mem_of_sum_mem_distinct_eigencharacters_mod k (HdR A₀) O ρ' (Fil A₀) hFst a χ hχ (fun i ↦ fstC A₀ (W j i) - fstC A₀ (W j₀ i))
      (fun i c ↦ by
        rw [hρ', map_sub, smul_sub, sub_sub_sub_comm]; exact sub_mem (hα j i c).1 (hα j₀ i c).1)
      (by
        rw [Finset.sum_sub_distrib]
        have := sub_mem (hs j₀).1 (hs j).1
        convert this using 1
        abel)

  choose w hw1 hw2 using fun i ↦ exists_of_coords (V := Fin d → k) hA (fstC A₀ (W j₀ i))
    (LinearMap.pi fun j ↦ (sndC A₀ (W j i) : HdR A₀) + f j (fstC A₀ (W j₀ i) - fstC A₀ (W j i)))
  refine ⟨w, fun i c ↦ ?_, ?_⟩
  · rw [push_sub_mem_glueFil_iff, hw1, hw2]
    refine ⟨(hα j₀ i c).1, fun j ↦ ?_⟩
    rw [LinearMap.proj_pi]
    have hδ : fstC A₀ (W j₀ i) - fstC A₀ (W j i) ∈ Fil A₀ := by
      have := neg_mem (hglue j i); rwa [neg_sub] at this
    have := add_mem (hα j i c).2 (hfstab j c _ hδ)
    convert this using 1
    simp only [map_add (f := _), map_sub, map_smul, smul_add, smul_sub]
    abel
  · rw [sub_sum_mem_glueFil_iff]
    simp only [hw1, hw2, LinearMap.proj_pi]
    refine ⟨(hs j₀).1, fun j ↦ ?_⟩
    convert (hs j).2 using 1

    simp only [Finset.sum_add_distrib, map_sub, map_sum, Finset.sum_sub_distrib]
    abel

end Core



theorem lie_glueFil : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] [IsAlgClosed k] (tk : R →+* k) (s : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s), s = spMap tk → ∀ (d : ℕ), 0 < d → ∀ (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), ∀ (E' : Fin d → Submodule (TrivSqZeroExt k k) (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A)), (∀ j, ∃ M : Submodule (TrivSqZeroExt k k) (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A), IsCompl (E' j) M) → (∀ j, ∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ e ∈ E' j, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k k)) rfl o₀.A).Corr e y) → (∀ j, ∀ x ∈ Fil o₀.A, ∃ e ∈ E' j, ∀ c, e ((GlobalTheory.FODef.constMorV k k o₀.A).pull c) = TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (f j x c)) → (∀ j (c : D.O), ∀ e ∈ E' j, (haveI := o₀.act.hom (c); push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (o₀.act.act (c)) (e)) ∈ E' j) → (∀ j, ∀ e : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω); push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) (e)) - ((algebraMap k (TrivSqZeroExt k k)).comp tk) b.ρ • e ∈ E' j → ∃ w : Fin D.a → Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c); push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - ((algebraMap k (TrivSqZeroExt k k)).comp tk) (b.t i c) • w i ∈ E' j) ∧ e - ∑ i, w i ∈ E' j) → ∀ e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω); push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) (e)) - ((algebraMap k (TrivSqZeroExt k (Fin d → k))).comp tk) b.ρ • e ∈ GlobalTheory.HTGlue.glueFil o₀.A f → ∃ w : Fin D.a → Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c); push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - ((algebraMap k (TrivSqZeroExt k (Fin d → k))).comp tk) (b.t i c) • w i ∈ GlobalTheory.HTGlue.glueFil o₀.A f) ∧ e - ∑ i, w i ∈ GlobalTheory.HTGlue.glueFil o₀.A f := by
  intro p _ D R _ b N k _ _ tk s o₀ _ d hd f E' hcompl hred hlift hstab hlie e he
  haveI hact : ∀ c : 𝓞 D.F, IsMonHom (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) := fun c ↦ o₀.act.hom _
  have L1j := fun j ↦ GlobalTheory.T.dualNumber_hodge_summand_eq_graph_coordinates k o₀.A o₀.ab (f j) (E' j) (hcompl j) (hred j) (hlift j)
  have hχ : ∀ i i', i ≠ i' → ∃ c : 𝓞 D.F, tk (b.t i c) ≠ tk (b.t i' c) := by
    intro i i' hii'
    by_contra hcon
    push_neg at hcon
    have hle : Ideal.span (Set.range fun x ↦ b.t i x - b.t i' x) ≤ RingHom.ker tk := by
      rw [Ideal.span_le]
      rintro _ ⟨x, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, hcon x, sub_self]
    have h1 : (1 : R) ∈ RingHom.ker tk := hle (b.comax i i' hii' ▸ Submodule.mem_top)
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  have hlift' : ∀ j, ∀ x ∈ Fil o₀.A, ∃ e ∈ E' j, fstC o₀.A e = x ∧ (sndC o₀.A e : HdR o₀.A) = f j x := by
    intro j x hx
    obtain ⟨e1, he1, h⟩ := hlift j x hx
    refine ⟨e1, he1, ?_, ?_⟩ <;> ext c
    · rw [fstC_apply, h c, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
    · rw [sndC_apply, h c, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
  exact core o₀.ab (fun c : 𝓞 D.F ↦ o₀.act.act (algebraMap (𝓞 D.F) D.O c))
    ((GlobalTheory.HTCount.crysAct o₀).comp (algebraMap (𝓞 D.F) D.O)) (fun _ _ ↦ rfl) D.ω (tk b.ρ)
    (fun i c ↦ tk (b.t i c)) hχ hd f E' L1j hlift' (fun j c e he ↦ hstab j _ e he) hlie e he

end GlobalTheory.HTGlueLie
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalGluedHodgeGraphLieConditionOfDirectionsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.crystalGluedHodgeGraph_lie_condition_of_directions : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] [IsAlgClosed k] (tk : R →+* k) (s : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s), s = spMap tk → ∀ (d : ℕ), 0 < d → ∀ (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), ∀ (E' : Fin d → Submodule (TrivSqZeroExt k k) (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A)), (∀ j, ∃ M : Submodule (TrivSqZeroExt k k) (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A), IsCompl (E' j) M) → (∀ j, ∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ e ∈ E' j, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k k)) rfl o₀.A).Corr e y) → (∀ j, ∀ x ∈ Fil o₀.A, ∃ e ∈ E' j, ∀ c, e ((GlobalTheory.FODef.constMorV k k o₀.A).pull c) = TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (f j x c)) → (∀ j (c : D.O), ∀ e ∈ E' j, (haveI := o₀.act.hom (c); push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (o₀.act.act (c)) (e)) ∈ E' j) → (∀ j, ∀ e : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω); push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) (e)) - ((algebraMap k (TrivSqZeroExt k k)).comp tk) b.ρ • e ∈ E' j → ∃ w : Fin D.a → Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c); push (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - ((algebraMap k (TrivSqZeroExt k k)).comp tk) (b.t i c) • w i ∈ E' j) ∧ e - ∑ i, w i ∈ E' j) → ∀ e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω); push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) (e)) - ((algebraMap k (TrivSqZeroExt k (Fin d → k))).comp tk) b.ρ • e ∈ GlobalTheory.HTGlue.glueFil o₀.A f → ∃ w : Fin D.a → Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c); push (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - ((algebraMap k (TrivSqZeroExt k (Fin d → k))).comp tk) (b.t i c) • w i ∈ GlobalTheory.HTGlue.glueFil o₀.A f) ∧ e - ∑ i, w i ∈ GlobalTheory.HTGlue.glueFil o₀.A f := by
  first | (exact @GlobalTheory.HTGlueLie.lie_glueFil) | (exact GlobalTheory.HTGlueLie.lie_glueFil) | (intros; apply GlobalTheory.HTGlueLie.lie_glueFil  <;> assumption)
end
end
