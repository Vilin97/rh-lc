module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMemConj
public import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMemConj
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairRegularImageAtP
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorMapEigenvalueNormBound

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.StabFin
open scoped TensorProduct Classical

namespace GlobalTheory.StabFin.IntBound

variable (p : ℕ) [Fact p.Prime] (Kw : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ)

noncomputable def mu : KQ p Kw r →+* PadicAlgCl p :=
  (Algebra.TensorProduct.lift Kw.val (Qr p r).val (fun _ _ => Commute.all _ _) :
    Kw ⊗[ℚ_[p]] Qr p r →ₐ[ℚ_[p]] PadicAlgCl p).toRingHom

theorem mu_inclK (a : Kw) : mu p Kw r (inclK p Kw r a) = (a : PadicAlgCl p) := by
  change (Algebra.TensorProduct.lift Kw.val (Qr p r).val (fun _ _ => Commute.all _ _)) (a ⊗ₜ[ℚ_[p]] (1 : Qr p r)) = _
  rw [Algebra.TensorProduct.lift_tmul]
  simp

theorem mu_inclQ (b : Qr p r) : mu p Kw r (inclQ p Kw r b) = (b : PadicAlgCl p) := by
  change (Algebra.TensorProduct.lift Kw.val (Qr p r).val (fun _ _ => Commute.all _ _)) ((1 : Kw) ⊗ₜ[ℚ_[p]] b) = _
  rw [Algebra.TensorProduct.lift_tmul]
  simp

theorem intKQ_le : intKQ p Kw r ≤ (ReciprocityTheory.DiscreteGroups.LocalClassField.Obar p).toSubring.comap (mu p Kw r) := by
  rw [intKQ, Subring.closure_le]
  rintro x (⟨a, rfl⟩ | ⟨b, rfl⟩)
  · change mu p Kw r (inclK p Kw r a) ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.Obar p
    rw [mu_inclK]
    exact a.2
  · change mu p Kw r (inclQ p Kw r b) ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.Obar p
    rw [mu_inclQ]
    exact b.2

theorem norm_mu_le_one (x : KQ p Kw r) (hx : x ∈ intKQ p Kw r) : ‖mu p Kw r x‖ ≤ 1 :=
  ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff.1 (intKQ_le p Kw r hx)

end GlobalTheory.StabFin.IntBound

namespace GlobalTheory.StabFin

theorem norm_eigen_le_one_of_conj_Kres : ∀ (p : ℕ) [Fact p.Prime] (Kw : IntermediateField ℚ_[p] (PadicAlgCl p))
    (n r : ℕ) (N : Matrix (Fin n) (Fin n) Kw) (H k : GL (Fin n) (KQ p Kw r)), k ∈ Kres p Kw n r →
    N.map (inclK p Kw r) = ((H * k * H⁻¹ : GL (Fin n) (KQ p Kw r)) : Matrix (Fin n) (Fin n) (KQ p Kw r)) →
    ∀ (v : Fin n → PadicAlgCl p) (c : PadicAlgCl p), v ≠ 0 →
      N.map (fun x => (x : PadicAlgCl p)) *ᵥ v = c • v → ‖c‖ ≤ 1 := by
  intro p _ Kw n r N H k hk hN v c hv hev
  set μ := IntBound.mu p Kw r
  set A := μ.mapMatrix (H : Matrix (Fin n) (Fin n) (KQ p Kw r))
  set Ai := μ.mapMatrix ((H⁻¹ : GL (Fin n) (KQ p Kw r)) : Matrix (Fin n) (Fin n) (KQ p Kw r))
  set B := μ.mapMatrix (k : Matrix (Fin n) (Fin n) (KQ p Kw r))
  have hAAi : A * Ai = 1 := by
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  have hAiA : Ai * A = 1 := by
    rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
  have hM : N.map (fun x => (x : PadicAlgCl p)) = A * B * Ai := by
    have h1 : N.map (fun x => (x : PadicAlgCl p)) = μ.mapMatrix (N.map (inclK p Kw r)) := by
      ext i j
      simp [μ, IntBound.mu_inclK]
    rw [h1, hN, Units.val_mul, Units.val_mul, map_mul, map_mul]
  set v' := Ai *ᵥ v
  have hv' : v' ≠ 0 := by
    intro h0
    apply hv
    have : A *ᵥ v' = v := by rw [mulVec_mulVec, hAAi, one_mulVec]
    rw [← this, h0, mulVec_zero]
  have hBv : B *ᵥ v' = c • v' := by
    have e1 : Ai *ᵥ (N.map (fun x => (x : PadicAlgCl p)) *ᵥ v) = c • v' := by
      rw [hev, mulVec_smul]
    rw [hM, mulVec_mulVec, ← mul_assoc, ← mul_assoc, hAiA, one_mul, ← mulVec_mulVec] at e1
    exact e1
  have hB : ∀ i j, ‖B i j‖ ≤ 1 := by
    obtain ⟨k0, rfl⟩ := hk
    intro i j
    simp only [B, RingHom.mapMatrix_apply, Matrix.map_apply, GeneralLinearGroup.map_apply]
    exact IntBound.norm_mu_le_one p Kw r _ (k0 i j).2
  haveI : Nonempty (Fin n) := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hv' (Subsingleton.elim _ _)
  obtain ⟨j, hj⟩ := Finite.exists_max (fun l => ‖v' l‖)
  have hpos : 0 < ‖v' j‖ := by
    rcases (norm_nonneg (v' j)).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hv'
      funext l
      have := hj l
      rw [← h] at this
      exact norm_le_zero_iff.1 this
  have key : ‖c‖ * ‖v' j‖ ≤ 1 * ‖v' j‖ := by
    have e : c * v' j = ∑ l, B j l * v' l := by
      have := congrFun hBv j
      rw [Pi.smul_apply, smul_eq_mul] at this
      rw [← this]
      rfl
    rw [← norm_mul, e, one_mul]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun l _ => ?_
    rw [norm_mul]
    calc ‖B j l‖ * ‖v' l‖ ≤ 1 * ‖v' j‖ :=
          mul_le_mul (hB j l) (hj l) (norm_nonneg _) zero_le_one
      _ = ‖v' j‖ := one_mul _
  exact le_of_mul_le_mul_right key hpos

end GlobalTheory.StabFin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenvalueIntegralNormBound

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.StabFin
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.eigenvalue_integral_norm_bound : ∀ (p : ℕ) [Fact p.Prime] (Kw : IntermediateField ℚ_[p] (PadicAlgCl p)) (n r : ℕ) (N : Matrix (Fin n) (Fin n) Kw) (H k : GL (Fin n) (KQ p Kw r)), k ∈ Kres p Kw n r → N.map (inclK p Kw r) = ((H * k * H⁻¹ : GL (Fin n) (KQ p Kw r)) : Matrix (Fin n) (Fin n) (KQ p Kw r)) → ∀ (v : Fin n → PadicAlgCl p) (c : PadicAlgCl p), v ≠ 0 → N.map (fun x => (x : PadicAlgCl p)) *ᵥ v = c • v → ‖c‖ ≤ 1 := by
  first | (exact @GlobalTheory.StabFin.norm_eigen_le_one_of_conj_Kres) | (exact GlobalTheory.StabFin.norm_eigen_le_one_of_conj_Kres) | (intros; apply GlobalTheory.StabFin.norm_eigen_le_one_of_conj_Kres  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonEigenvectorRhoAdjoinRootEmbedding

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.StabFin
open scoped TensorProduct Classical

namespace GlobalTheory.StabFin

theorem rho_jM_common_eigvec : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (i : Fin G.m)
    (τ : FM P →+* PadicAlgCl p), τ.comp (algebraMap G.F (FM P)) = G.emb i →
    ∃ v : Fin G.n → PadicAlgCl p, v ≠ 0 ∧
      ∀ a : FM P, (G.rho i (jM P a)).map (fun x => (x : PadicAlgCl p)) *ᵥ v = τ a • v := by
  intro p _ G P i τ hτ
  let f : G.Fw i →+* PadicAlgCl p := algebraMap (G.Fw i) (PadicAlgCl p)
  have hf : (fun x : G.Fw i => (x : PadicAlgCl p)) = ⇑f := rfl
  have hfe : f.comp (G.embW i) = G.emb i := by
    ext x; rfl
  let ψ : G.C →+* Matrix (Fin G.n) (Fin G.n) (PadicAlgCl p) := f.mapMatrix.comp (G.rho i)
  have hψ : ∀ x, ψ x = (G.rho i x).map (fun x => (x : PadicAlgCl p)) := fun x => rfl
  set M := ψ (P.γ : G.C) with hM
  set lam := τ (AdjoinRoot.root P.pol) with hlam
  have hchar : M.charpoly = P.pol.map (G.emb i) := by
    rw [hM, hψ, hf, Matrix.charpoly_map, charpoly_rho_eq_map_pol, Polynomial.map_map, hfe]
  have heval : Polynomial.eval lam M.charpoly = 0 := by
    rw [hchar, Polynomial.eval_map, ← hτ, ← Polynomial.hom_eval₂, AdjoinRoot.algebraMap_eq,
      AdjoinRoot.eval₂_root, map_zero]
  rw [Matrix.eval_charpoly] at heval
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 heval
  have hMv : M *ᵥ v = lam • v := by
    rw [Matrix.sub_mulVec, sub_eq_zero] at hv
    rw [← hv]
    ext j
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  refine ⟨v, hv0, fun a => ?_⟩
  rw [← hψ]
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective a
  rw [jM_mk]
  have key : ∀ g : Polynomial G.F, ψ (Polynomial.aeval (P.γ : G.C) g) *ᵥ v =
      τ (AdjoinRoot.mk P.pol g) • v := by
    intro g
    induction g using Polynomial.induction_on with
    | C c =>
      rw [Polynomial.aeval_C, AdjoinRoot.mk_C, ← AdjoinRoot.algebraMap_eq, ← RingHom.comp_apply τ, hτ]
      show (f.mapMatrix (G.rho i (algebraMap G.F G.C c))) *ᵥ v = _
      rw [G.rho_F]
      ext j
      simp [Matrix.scalar_apply, Matrix.mulVec_diagonal, RingHom.mapMatrix_apply, Matrix.diagonal_map]
      exact Or.inl rfl
    | add g h hg hh =>
      rw [map_add (f := _), map_add (f := _), Matrix.add_mulVec, hg, hh, map_add (f := _), map_add (f := _), add_smul]
    | monomial k c hk =>
      rw [pow_succ, ← mul_assoc, map_mul, map_mul, ← Matrix.mulVec_mulVec, Polynomial.aeval_X, ← hM, hMv,
        Matrix.mulVec_smul, hk, smul_smul]
      congr 1
      rw [map_mul (AdjoinRoot.mk P.pol) _ Polynomial.X, map_mul τ, AdjoinRoot.mk_X, mul_comm]
  exact key g

end GlobalTheory.StabFin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonEigenvectorRhoAdjoinRootEmbeddingStatement

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.StabFin
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.exists_common_eigenvector_rho_adjoinRoot_embedding : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (i : Fin G.m) (τ : FM P →+* PadicAlgCl p), τ.comp (algebraMap G.F (FM P)) = G.emb i → ∃ v : Fin G.n → PadicAlgCl p, v ≠ 0 ∧ ∀ a : FM P, (G.rho i (jM P a)).map (fun x => (x : PadicAlgCl p)) *ᵥ v = τ a • v := by
  first | (exact @GlobalTheory.StabFin.rho_jM_common_eigvec) | (exact GlobalTheory.StabFin.rho_jM_common_eigvec) | (intros; apply GlobalTheory.StabFin.rho_jM_common_eigvec  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenvalueNormBound

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.StabFin
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.StabFin

theorem norm_le_one_at_u : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (r : ℕ) (z : Gr G r) (K : Subgroup (Gr G r)) (g : Gr G r), 0 < r → Subgroup.Commensurable K (KHT p G.m G.n r G.Fw) → ∀ w : P.cent, P.toQr r z w ∈ K.map (MulAut.conj g).toMonoidHom → ∀ (a : FM P), jM P a = ((w : G.Cˣ × ℚˣ).1 : G.C) → ∀ τ : FM P →+* PadicAlgCl p, LiesOver G.Kq G.u (τ.comp (algebraMap G.F (FM P))) → ‖τ a‖ ≤ 1 := by
  intro p _ G P r z K g _ hK w hw a ha τ hτ
  obtain ⟨i, σ, hσ⟩ := G.emb_all _ hτ
  set τ' : FM P →+* PadicAlgCl p := ((σ.symm : PadicAlgCl p ≃+* PadicAlgCl p) : PadicAlgCl p →+* PadicAlgCl p).comp τ with hτ'
  have hτ'F : τ'.comp (algebraMap G.F (FM P)) = G.emb i := by
    rw [hτ', RingHom.comp_assoc, hσ]
    ext x; simp
  have hnorm : ‖τ a‖ = ‖τ' a‖ := by
    have : τ a = σ (τ' a) := by simp [hτ']
    rw [this]; exact (spectralNorm_eq_of_equiv σ _).symm
  rw [hnorm]
  obtain ⟨m, hm0, hm⟩ := exists_pow_mem_conj K (KHT p G.m G.n r G.Fw) g _ hK hw
  obtain ⟨k, hk, hkeq⟩ := hm
  obtain ⟨v, hv0, hv⟩ := GlobalTheory.T.exists_common_eigenvector_rho_adjoinRoot_embedding p G P i τ' hτ'F
  have hjm : jM P (a ^ m) = (((w ^ m : P.cent) : G.Cˣ × ℚˣ).1 : G.C) := by
    rw [map_pow, ha]; rfl
  have key : (z * g) * k * (z * g)⁻¹ = inclG G r (locC G ((w ^ m : P.cent) : G.Cˣ × ℚˣ)) := by
    have e : P.toQr r z (w ^ m) = z⁻¹ * inclG G r (locC G ((w ^ m : P.cent) : G.Cˣ × ℚˣ)) * z := rfl
    rw [map_pow] at e
    rw [← hkeq] at e
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at e
    have e2 : inclG G r (locC G ((w ^ m : P.cent) : G.Cˣ × ℚˣ)) =
        z * (z⁻¹ * inclG G r (locC G ((w ^ m : P.cent) : G.Cˣ × ℚˣ)) * z) * z⁻¹ := by group
    rw [e2, ← e]
    group
  have hcomp := congrArg (fun x : Gr G r => ((x.2 i : GL (Fin G.n) (KQ p (G.Fw i) r)) : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw i) r))) key
  have hk' : k.2 i ∈ Kres p (G.Fw i) G.n r := hk.2 i (Set.mem_univ _)
  have hb := GlobalTheory.T.eigenvalue_integral_norm_bound p (G.Fw i) G.n r (G.rho i (jM P (a ^ m))) ((z * g).2 i) (k.2 i) hk'
    (by rw [hjm]; exact hcomp.symm) v (τ' (a ^ m)) hv0 (hv _)
  rw [map_pow, norm_pow] at hb
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hm0.ne').1 hb

end GlobalTheory.StabFin
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerElementPadicBounded

section

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.StabFin
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.centralizer_element_padic_bounded : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (r : ℕ) (z : Gr G r) (K : Subgroup (Gr G r)) (g : Gr G r), 0 < r → Subgroup.Commensurable K (KHT p G.m G.n r G.Fw) → ∀ w : P.cent, P.toQr r z w ∈ K.map (MulAut.conj g).toMonoidHom → ∀ (a : FM P), jM P a = ((w : G.Cˣ × ℚˣ).1 : G.C) → ∀ τ : FM P →+* PadicAlgCl p, LiesOver G.Kq G.u (τ.comp (algebraMap G.F (FM P))) → ‖τ a‖ ≤ 1 := by
  first | (exact @GlobalTheory.StabFin.norm_le_one_at_u) | (exact GlobalTheory.StabFin.norm_le_one_at_u) | (intros; apply GlobalTheory.StabFin.norm_le_one_at_u  <;> assumption)
end
end
