module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LiftFrameEmbeddingBase
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockDataOfCongruentHeckeSystemStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCharZeroEigenformSurvivingCompositionFacto
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisLiftResidueCongruencePadicStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearActionDualWeylTensor
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimpleModuleLinkageDualWeylLatticeReductionStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCharZeroEigenformSurvivingCompositionFactoStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

theorem _root_.GlobalTheory.T.exists_charZero_eigenform_surviving_compositionFactor : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ) (mu : ι → ℕ → ℕ) (jK : F.K →* alg F.O N lam) (ϖ : F.O), F.Ok → F.IsJ lam jK → Irreducible ϖ → ∀ (Gm : Type) [AddCommGroup Gm] [Module F.O Gm] [Module (alg F.O N lam) Gm] [IsScalarTower F.O (alg F.O N lam) Gm] [Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK Gm)], F.IsHecke lam jK Gm → Embeds F.O N lam mu ϖ Gm → ∀ (m : Ideal F.T) [m.IsMaximal], ¬ Subsingleton (LocalizedModule m.primeCompl (Forms F.O (A := alg F.O N lam) F.Γ jK Gm)) → ∃ θ, F.IsEig mu θ ∧ F.Over θ m := by
  first | exact @GlobalTheory.ExpFrame.Eigenform.eigenform_of_surviving | exact GlobalTheory.ExpFrame.Eigenform.eigenform_of_surviving | (intros; apply GlobalTheory.ExpFrame.Eigenform.eigenform_of_surviving <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearActionDualWeylTensorStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

theorem _root_.GlobalTheory.T.exists_semilinear_action_dualWeylTensor : ∀ (R : Type) [CommRing R] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (mu : ι → ℕ → ℕ) (g : R ≃+* R), ∃ Φ : NablaT R N mu →+ NablaT R N mu, Function.Injective Φ ∧ (∀ (c : R) x, Φ (c • x) = g c • Φ x) ∧ ∀ (h : ι → GL (Fin N) R), (∀ τ a b, g ((h τ : Matrix (Fin N) (Fin N) R) a b) = (h τ : Matrix (Fin N) (Fin N) R) a b) → ∀ x, Φ (grp R N mu h x) = grp R N mu h (Φ x) := by
  first | exact @GlobalTheory.semilinear_transport | exact GlobalTheory.semilinear_transport | (intros; apply GlobalTheory.semilinear_transport <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisConjEigenSystemCongruent

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

namespace GlobalTheory.ExpFrame.Conj

theorem isEig_map {l : ℕ} [Fact l.Prime] {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (F : Frame l ι N)
    (mu : ι → ℕ → ℕ) (g : PadicAlgCl l ≃+* PadicAlgCl l) (hg : ∀ x, g (F.emb x) = F.emb x)
    (θ : F.I → PadicAlgCl l) (h : F.IsEig mu θ) : F.IsEig mu (fun i => g (θ i)) := by
  obtain ⟨f, hf0, ⟨hΓ, hK⟩, hH⟩ := h
  obtain ⟨Φ, hinj, hsm, hgrp⟩ := GlobalTheory.T.exists_semilinear_action_dualWeylTensor (PadicAlgCl l) ι N mu g
  refine ⟨fun x => Φ (f x), ?_, ⟨fun γ hγ x => by simp only [hΓ γ hγ x], fun κ x => ?_⟩, fun i x => ?_⟩
  · intro h0
    apply hf0
    funext x
    have := congrFun h0 x
    exact hinj (by simpa using this)
  · have hfix : ∀ τ a b, g ((Matrix.GeneralLinearGroup.map F.emb (F.kap κ τ) : Matrix (Fin N) (Fin N) (PadicAlgCl l)) a b) =
        (Matrix.GeneralLinearGroup.map F.emb (F.kap κ τ) : Matrix (Fin N) (Fin N) (PadicAlgCl l)) a b := by
      intro τ a b
      simp [hg]
    rw [← hgrp _ hfix, ← hg (F.chi κ : F.O), ← hsm, hK κ x]
  · have := hH i x
    simp only

    rw [← hg (F.cst i), ← map_sum, ← hsm, this, hsm]

theorem exists_eig_congr : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ), F.Ok → ∀ (θ θ0 : F.I → PadicAlgCl l) (m : Ideal F.T), F.IsEig lam θ → F.Over θ m → F.Over θ0 m → ∃ θ', F.IsEig lam θ' ∧ (∀ i, ‖θ' i‖ ≤ 1) ∧ ∀ i, ‖θ' i - θ0 i‖ < 1 := by
  intro l _ ι _ _ N F lam hOk θ θ0 m hE hθ hθ0
  obtain ⟨_, L, hfin, hrange⟩ := hOk.ring
  have hmemL : ∀ x, F.emb x ∈ L := fun x => by
    have : F.emb x ∈ Set.range F.emb := ⟨x, rfl⟩
    rw [hrange] at this
    exact this.1
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_galois_lift_residue_congruence_padic l L F.I θ θ0 hθ.1 hθ0.1 (by
    intro p hp
    have hmem : p ∈ Set.range (MvPolynomial.map F.emb) := by
      rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
      intro c hc
      obtain ⟨n, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.1 hc
      rw [hrange]
      exact hp n
    obtain ⟨q, rfl⟩ := hmem
    rw [MvPolynomial.eval_map, MvPolynomial.eval_map, ← hθ.2 q, hθ0.2 q])
  have hn : ∀ x, ‖g x‖ = ‖x‖ := fun x => (spectralNorm_eq_of_equiv (g.restrictScalars ℚ_[l]) x).symm
  refine ⟨fun i => g (θ i), isEig_map F lam g.toRingEquiv (fun x => g.commutes ⟨F.emb x, hmemL x⟩) θ hE,
    fun i => (hn _).trans_le (hθ.1 i), hg⟩

end GlobalTheory.ExpFrame.Conj
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisConjEigenSystemCongruentStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

theorem _root_.GlobalTheory.T.exists_galoisConj_eigenSystem_congruent : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ), F.Ok → ∀ (θ θ0 : F.I → PadicAlgCl l) (m : Ideal F.T), F.IsEig lam θ → F.Over θ m → F.Over θ0 m → ∃ θ', F.IsEig lam θ' ∧ (∀ i, ‖θ' i‖ ≤ 1) ∧ ∀ i, ‖θ' i - θ0 i‖ < 1 := by
  first | exact @GlobalTheory.ExpFrame.Conj.exists_eig_congr | exact GlobalTheory.ExpFrame.Conj.exists_eig_congr | (intros; apply GlobalTheory.ExpFrame.Conj.exists_eig_congr <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeLinkOfSurvivingSimpleSubquotient

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

theorem GlobalTheory.ExpFrame.LinkQ.latticeLink_of_surviving : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω], GlobalTheory.Published.ChebotarevDegreeOne → ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (inc : ι → (E →+* PadicAlgCl l)) (fr : ℕ → ι → ι) (cjj : ℕ → ι → Bool) (P : Par) (W : Wts ι), (∀ mu : ι → ℕ → ℕ, Linked l P.Nr W.lam mu → BlockFor Ω inc P W mu → ∀ τ, LatticeLink P (reFr W fr cjj) l τ (res P.Nr (mu τ))) → ∀ (F : Frame l ι P.Nr), F.Ok → ∀ (Bk : (F.I → PadicAlgCl l) → Prop), GalSide Ω inc P W F Bk → ∀ (jK : F.K →* alg F.O P.Nr W.lam), F.IsJ W.lam jK → ∀ (ϖ : F.O), Irreducible ϖ → ϖ ∣ ((l : ℕ) : F.O) → (∀ τ, Antitone (res P.Nr (W.lam τ))) → ∀ (Gm : Type) [AddCommGroup Gm] [Module F.O Gm] [Module (alg F.O P.Nr W.lam) Gm] [IsScalarTower F.O (alg F.O P.Nr W.lam) Gm] [Module F.T (Forms F.O (A := alg F.O P.Nr W.lam) F.Γ jK Gm)], F.IsHecke W.lam jK Gm → IsSimpleModule (alg F.O P.Nr W.lam) Gm → SubQ F.O P.Nr W.lam ϖ Gm → ∀ (mu : ι → ℕ → ℕ), (∀ τ, Antitone (res P.Nr (mu τ)) ∧ ∑ a : Fin P.Nr, mu τ a = ∑ a : Fin P.Nr, W.lam τ a ∧ (∀ a : Fin P.Nr, W.lam τ (P.Nr - 1) ≤ mu τ a ∧ mu τ a ≤ W.lam τ 0)) → Embeds F.O P.Nr W.lam mu ϖ Gm → ∀ (m : Ideal F.T) [m.IsMaximal] (θ0 : F.I → PadicAlgCl l), F.IsEig W.lam θ0 → Bk θ0 → F.Over θ0 m → ¬ Subsingleton (LocalizedModule m.primeCompl (Forms F.O (A := alg F.O P.Nr W.lam) F.Γ jK Gm)) → ∀ τ, LatticeLink P (reFr W fr cjj) l τ (res P.Nr (mu τ)) := by
  intro E Ω _ _ _ _ _ _ hCheb l _ ι _ _ inc fr cjj P W hlink F hF Bk hG jK hJ ϖ hϖ hϖl hlam Gm _ _ _ _ _ hH hS hSQ mu hmu hemb m _ θ0 h0e h0b h0o hns
  obtain ⟨θ, hθe, hθo⟩ := GlobalTheory.T.exists_charZero_eigenform_surviving_compositionFactor l ι P.Nr F W.lam mu jK ϖ hF hJ hϖ Gm hH hemb m hns
  obtain ⟨θ', hθ'e, -, hc⟩ := GlobalTheory.T.exists_galoisConj_eigenSystem_congruent l ι P.Nr F mu hF θ θ0 m hθe hθo h0o
  have hB : BlockFor Ω inc P W mu :=
    GlobalTheory.T.blockData_of_congruent_heckeSystem hCheb E Ω l ι inc P W F Bk hG mu θ' θ0 (fun τ => (hmu τ).1) hθ'e h0e h0b hc
  have hnt : Nontrivial Gm := IsSimpleModule.nontrivial (alg F.O P.Nr W.lam) Gm
  have hlnk := GlobalTheory.T.simpleModule_linkage_dualWeylLattice_reduction F.O P.Nr ι W.lam mu l ϖ (Fact.out) hϖ hϖl hlam (fun τ => (hmu τ).1) Gm hnt hSQ hemb
  exact hlink mu (fun τ => ⟨(hmu τ).1, (hmu τ).2.1, (hmu τ).2.2, hlnk τ⟩) hB
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeLinkOfSurvivingSimpleSubquotientStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

theorem _root_.GlobalTheory.T.latticeLink_of_surviving_simple_subquotient : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω], GlobalTheory.Published.ChebotarevDegreeOne → ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (inc : ι → (E →+* PadicAlgCl l)) (fr : ℕ → ι → ι) (cjj : ℕ → ι → Bool) (P : Par) (W : Wts ι), (∀ mu : ι → ℕ → ℕ, Linked l P.Nr W.lam mu → BlockFor Ω inc P W mu → ∀ τ, LatticeLink P (reFr W fr cjj) l τ (res P.Nr (mu τ))) → ∀ (F : Frame l ι P.Nr), F.Ok → ∀ (Bk : (F.I → PadicAlgCl l) → Prop), GalSide Ω inc P W F Bk → ∀ (jK : F.K →* alg F.O P.Nr W.lam), F.IsJ W.lam jK → ∀ (ϖ : F.O), Irreducible ϖ → ϖ ∣ ((l : ℕ) : F.O) → (∀ τ, Antitone (res P.Nr (W.lam τ))) → ∀ (Gm : Type) [AddCommGroup Gm] [Module F.O Gm] [Module (alg F.O P.Nr W.lam) Gm] [IsScalarTower F.O (alg F.O P.Nr W.lam) Gm] [Module F.T (Forms F.O (A := alg F.O P.Nr W.lam) F.Γ jK Gm)], F.IsHecke W.lam jK Gm → IsSimpleModule (alg F.O P.Nr W.lam) Gm → SubQ F.O P.Nr W.lam ϖ Gm → ∀ (mu : ι → ℕ → ℕ), (∀ τ, Antitone (res P.Nr (mu τ)) ∧ ∑ a : Fin P.Nr, mu τ a = ∑ a : Fin P.Nr, W.lam τ a ∧ (∀ a : Fin P.Nr, W.lam τ (P.Nr - 1) ≤ mu τ a ∧ mu τ a ≤ W.lam τ 0)) → Embeds F.O P.Nr W.lam mu ϖ Gm → ∀ (m : Ideal F.T) [m.IsMaximal] (θ0 : F.I → PadicAlgCl l), F.IsEig W.lam θ0 → Bk θ0 → F.Over θ0 m → ¬ Subsingleton (LocalizedModule m.primeCompl (Forms F.O (A := alg F.O P.Nr W.lam) F.Γ jK Gm)) → ∀ τ, LatticeLink P (reFr W fr cjj) l τ (res P.Nr (mu τ)) := by
  first | exact @GlobalTheory.ExpFrame.LinkQ.latticeLink_of_surviving | exact GlobalTheory.ExpFrame.LinkQ.latticeLink_of_surviving | (intros; apply GlobalTheory.ExpFrame.LinkQ.latticeLink_of_surviving <;> assumption)
end
end
