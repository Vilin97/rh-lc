module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.FactorApply
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelInfAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealmapsIsomorphism
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsOrbitKernel

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct
open scoped Matrix

noncomputable section

namespace GlobalTheory.HoweGlobalPair.FinPlaceSmall

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem one_mem_UAt {n : ℕ} (X : Spc F E n) {R : Type} [Zero R] (ev : AF F → R) : (1 : UA σ X.J) ∈ UAt σ X ev := by
  intro u _
  have e : mat (1 : UA σ X.J) = 1 := rfl
  show u • (mat (1 : UA σ X.J) - 1) = 0
  rw [e, sub_self, smul_zero]

variable {Bs : Base F E} {a a' : ℕ} {G : Geo σ a a'} {Xc : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem exists_image (hT : IsTriple Bs G Xc om om') (v : Pl (F := F)) {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evFin F v))
    (φ : (Fin a' × Fin (a + a') → Fv F v) → ℂ) (hφ : φ ∈ SB (Fin a' × Fin (a + a') → Fv F v)) :
    ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (1, h)) φ φ₁ :=
  GlobalTheory.ThK.LocalOps.acts_exists (GlobalTheory.ThK.RealUniq.isPair_V' hT) v (1, h) (one_mem_UAt _ _) hh φ hφ

def locOp (hT : IsTriple Bs G Xc om om') (v : Pl (F := F)) {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evFin F v)) :
    Module.End ℂ ↥(SB (Fin a' × Fin (a + a') → Fv F v)) where
  toFun φ := ⟨Classical.choose (exists_image hT v hh φ φ.2), (Classical.choose_spec (exists_image hT v hh φ φ.2)).1⟩
  map_add' φ ψ := by
    apply Subtype.ext
    have hφ := (Classical.choose_spec (exists_image hT v hh φ φ.2)).2
    have hψ := (Classical.choose_spec (exists_image hT v hh ψ ψ.2)).2
    have hs := (Classical.choose_spec (exists_image hT v hh (φ + ψ : ↥(SB _)) (φ + ψ).2)).2
    have hl := GlobalTheory.ThK.LocalOps.acts_lin v (om' (1, h)) (fun χ hχ => exists_image hT v hh χ hχ) φ.2 ψ.2 hφ hψ 1 1
    simp only [one_smul] at hl
    exact GlobalTheory.ThK.LocalOps.acts_unique v _ (φ + ψ).2 hs hl
  map_smul' c φ := by
    apply Subtype.ext
    have hφ := (Classical.choose_spec (exists_image hT v hh φ φ.2)).2
    have hs := (Classical.choose_spec (exists_image hT v hh (c • φ : ↥(SB _)) (c • φ).2)).2
    have hl := GlobalTheory.ThK.LocalOps.acts_lin v (om' (1, h)) (fun χ hχ => exists_image hT v hh χ hχ) φ.2 φ.2 hφ hφ c 0
    simp only [zero_smul, add_zero] at hl
    exact GlobalTheory.ThK.LocalOps.acts_unique v _ (c • φ).2 hs hl

theorem locOp_acts (hT : IsTriple Bs G Xc om om') (v : Pl (F := F)) {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evFin F v))
    (φ : ↥(SB (Fin a' × Fin (a + a') → Fv F v))) :
    Acts (evFin F v) (om' (1, h)) (φ : (Fin a' × Fin (a + a') → Fv F v) → ℂ)
      ((locOp hT v hh φ : ↥(SB (Fin a' × Fin (a + a') → Fv F v))) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) :=
  (Classical.choose_spec (exists_image hT v hh φ φ.2)).2

theorem locOp_mem (hT : IsTriple Bs G Xc om om') (v : Pl (F := F)) {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evFin F v)) :
    locOp hT v hh ∈ GlobalTheory.HoweGlobalPair.opFin om' v :=
  ⟨h, hh, locOp_acts hT v hh⟩

end GlobalTheory.HoweGlobalPair.FinPlaceSmall
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.KerVp

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open UpperTheory.Lit.HoweDuality GlobalTheory.HoweGlobalPair

theorem UpperTheory.Lit.HoweDuality.kerVp :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {Bs : Base F E} {a a' : ℕ} {G : Geo σ a a'} {Xc : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} {R : RealMaps F a a'} {Rf : FinMaps F a a'}, IsMatched Bs G Xc om om' R Rf → ∀ v : Pl (F := F), relFin om' v ≤ LinearMap.ker (Rf.p' v ∘ₗ (SB (Fin a' × Fin (a + a') → Fv F v)).subtype) ∧ Stable (opFin om' v) (LinearMap.ker (Rf.p' v ∘ₗ (SB (Fin a' × Fin (a + a') → Fv F v)).subtype)) ∧ LinearMap.ker (Rf.p' v ∘ₗ (SB (Fin a' × Fin (a + a') → Fv F v)).subtype) ≠ ⊤ ∧ ∀ N : Submodule ℂ ↥(SB (Fin a' × Fin (a + a') → Fv F v)), LinearMap.ker (Rf.p' v ∘ₗ (SB (Fin a' × Fin (a + a') → Fv F v)).subtype) ≤ N → Stable (opFin om' v) N → N ≠ ⊤ → N ≤ LinearMap.ker (Rf.p' v ∘ₗ (SB (Fin a' × Fin (a + a') → Fv F v)).subtype) := by
  intro F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM v
  have hz : ∀ (h : UA σ G.W.J), Acts (evFin F v) (om (1, h))
      (0 : (Fin a × Fin (a + a') → Fv F v) → ℂ) 0 := by
    intro h r _
    have h0 : tens (evFin F v) (0 : (Fin a × Fin (a + a') → Fv F v) → ℂ) r = 0 := by
      funext x
      simp [tens]
    rw [h0, map_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [LinearMap.mem_ker, LinearMap.comp_apply]
    exact hM.fin.inv' v hx
  · rintro g ⟨h, hh, hg⟩ x hx
    rw [LinearMap.mem_ker, LinearMap.comp_apply] at hx ⊢
    have e := hM.fin.equiv v h hh 0 (Submodule.zero_mem _) x x.2 0 (Submodule.zero_mem _)
      (g x) (g x).2 (hz h) (hg x) (by rw [map_zero]; exact hx.symm)
    rw [map_zero] at e
    exact e.symm
  · intro hK
    haveI := hM.fin.nontriv v
    obtain ⟨y, hy⟩ := exists_ne (0 : Rf.Pi v)
    have hmem : y ∈ Submodule.map (Rf.p' v) (SB (Fin a' × Fin (a + a') → Fv F v)) := by
      rw [hM.fin.onto' v]
      exact Submodule.mem_top
    obtain ⟨φ, hφ, rfl⟩ := hmem
    have hk : (⟨φ, hφ⟩ : SB (Fin a' × Fin (a + a') → Fv F v)) ∈
        LinearMap.ker (Rf.p' v ∘ₗ (SB (Fin a' × Fin (a + a') → Fv F v)).subtype) := by
      rw [hK]
      exact Submodule.mem_top
    rw [LinearMap.mem_ker, LinearMap.comp_apply] at hk
    exact hy hk
  · intro N hKN hN hNtop
    have hst : ∀ h ∈ UAt σ G.W (evFin F v),
        ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
          ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
            Acts (evFin F v) (om (1, h)) φ φ₁ →
              Rf.p v φ ∈ Submodule.map (Rf.p' v) (Submodule.map (SB (Fin a' × Fin (a + a') → Fv F v)).subtype N) →
              Rf.p v φ₁ ∈ Submodule.map (Rf.p' v) (Submodule.map (SB (Fin a' × Fin (a + a') → Fv F v)).subtype N) := by
      intro h hh φ hφ φ₁ hφ₁ hact hp
      obtain ⟨y, ⟨n, hn, rfl⟩, hpn⟩ := hp
      have hgn := hN _ (GlobalTheory.HoweGlobalPair.FinPlaceSmall.locOp_mem hM.triple v hh) n hn
      have e := hM.fin.equiv v h hh φ hφ n n.2 φ₁ hφ₁ _ (GlobalTheory.HoweGlobalPair.FinPlaceSmall.locOp hM.triple v hh n).2
        hact (GlobalTheory.HoweGlobalPair.FinPlaceSmall.locOp_acts hM.triple v hh n) hpn.symm
      exact ⟨_, ⟨_, hgn, rfl⟩, e.symm⟩
    rcases hM.fin.irred v _ hst with hbot | htop
    · intro x hx
      have hm : Rf.p' v x ∈ Submodule.map (Rf.p' v) (Submodule.map (SB (Fin a' × Fin (a + a') → Fv F v)).subtype N) :=
        ⟨x, ⟨x, hx, rfl⟩, rfl⟩
      rw [hbot, Submodule.mem_bot] at hm
      rw [LinearMap.mem_ker, LinearMap.comp_apply]
      exact hm
    · exfalso
      apply hNtop
      rw [eq_top_iff]
      intro x _
      have hm : Rf.p' v x ∈ Submodule.map (Rf.p' v) (Submodule.map (SB (Fin a' × Fin (a + a') → Fv F v)).subtype N) := by
        rw [htop]
        exact Submodule.mem_top
      obtain ⟨y, ⟨n, hn, rfl⟩, hpn⟩ := hm
      have hk : x - n ∈ N := by
        apply hKN
        rw [LinearMap.mem_ker, LinearMap.comp_apply, map_sub, map_sub, sub_eq_zero]
        exact hpn.symm
      have := N.add_mem hk hn
      rwa [sub_add_cancel] at this
end
end
