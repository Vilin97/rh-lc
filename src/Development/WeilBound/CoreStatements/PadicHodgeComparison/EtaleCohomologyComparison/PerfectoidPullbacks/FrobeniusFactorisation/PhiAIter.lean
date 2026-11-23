module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.ExistsAlpha
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.NuPull
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.TwistedRepresentations.Tens
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinianLimitLiftOfCompatibleStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthOfLseqFirstStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitDivisibleOfVanishingLevelStatement
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import ReciprocityTheory.GroupCohomology.FinGen
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.LsSeqEq
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.SmoothModelFiniteLengthLink
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PeriodBaseChange.BcTens
import Mathlib.RingTheory.RegularLocalRing.Defs

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundedCokernelLimitToLevel

section

@[expose] public section

open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw

namespace GlobalTheory.CompanionTheory.TwCok

theorem pow_torsion_bounded {W : Type} [CommRing W] [IsNoetherianRing W] (r : W) (T : Type 1)
    [AddCommGroup T] [Module W T] [Module.Finite W T] :
    ∃ c : ℕ, ∀ (k : ℕ) (t : T), r ^ k • t = 0 → r ^ c • t = 0 := by
  haveI := isNoetherian_of_isNoetherianRing_of_finite W T
  let f : ℕ →o Submodule W T :=
    ⟨fun k => LinearMap.ker ((r ^ k) • LinearMap.id : T →ₗ[W] T), fun a b hab t ht => by
      simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] at ht ⊢
      obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
      rw [pow_add, mul_comm, mul_smul, ht, smul_zero]⟩
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance f
  refine ⟨n, fun k t ht => ?_⟩
  rcases le_total k n with hkn | hnk
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hkn
    rw [pow_add, mul_comm, mul_smul, ht, smul_zero]
  · have h1 : t ∈ f k := by
      simp only [f, OrderHom.coe_mk, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]
      exact ht
    rw [← hn k hnk] at h1
    have h2 : t ∈ LinearMap.ker ((r ^ n) • LinearMap.id : T →ₗ[W] T) := h1
    rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] at h2
    exact h2

variable {W : Type} [CommRing W] {l : ℕ} {S S' : Sys.{1} W}

def conn (Q : LSeq l S S') (n : ℕ) (x : S.M n) : S'.lim :=
  ⟨fun a => Q.δ n a x, fun a => Q.δ_r n a x⟩

theorem conn_smul (Q : LSeq l S S') (n : ℕ) (s : W) (x : S.M n) :
    s • conn Q n x = conn Q n (s • x) := by
  apply Subtype.ext
  funext a
  simp [conn]

theorem conn_kill (Q : LSeq l S S') (n : ℕ) (x : S.M n) : ((l : W) ^ n) • conn Q n x = 0 := by
  rw [conn_smul, Q.kill n x]
  apply Subtype.ext
  funext a
  simp [conn]

theorem lift_of_conn_zero (Q : LSeq l S S') (hA : ∀ n, IsArtinian W (S.M n)) (n : ℕ) (x : S.M n)
    (h : ∀ a, Q.δ n a x = 0) : ∃ y : S.lim, y.1 n = x := by
  classical
  have hy : ∀ m, n ≤ m → ∃ u : S.M m, Q.ρ m n u = x := fun m hm =>
    Q.ex₂ (m - n) n m (by omega) x (h _)
  let y : ∀ m, S.M m := fun m => if hm : n ≤ m then (hy m hm).choose else 0
  have hyx : ∀ m (hm : n ≤ m), Q.ρ m n (y m) = x := by
    intro m hm
    simp only [y, dif_pos hm]
    exact (hy m hm).choose_spec
  let N : ∀ m, Submodule W (S.M m) := fun m => if n ≤ m then LinearMap.ker (Q.ρ m n) else ⊤
  have hN : ∀ m (hm : n ≤ m), N m = LinearMap.ker (Q.ρ m n) := fun m hm => if_pos hm
  have hN' : ∀ m (hm : ¬ n ≤ m), N m = ⊤ := fun m hm => if_neg hm
  have hNr : ∀ m, ∀ u ∈ N (m + 1), S.r m u ∈ N m := by
    intro m u hu
    by_cases hm : n ≤ m
    · rw [hN (m + 1) (by omega), LinearMap.mem_ker] at hu
      rw [hN m hm, LinearMap.mem_ker, ← Q.ρ_succ m n hm]
      exact hu
    · rw [hN' m hm]
      exact Submodule.mem_top
  have hyr : ∀ m, S.r m (y (m + 1)) - y m ∈ N m := by
    intro m
    by_cases hm : n ≤ m
    · rw [hN m hm, LinearMap.mem_ker, map_sub, ← Q.ρ_succ m n hm, hyx (m + 1) (by omega), hyx m hm,
        sub_self]
    · rw [hN' m hm]
      exact Submodule.mem_top
  obtain ⟨z, hz⟩ := GlobalTheory.T.artinian_limit_lift_of_compatible W S hA N y hNr hyr
  refine ⟨z, ?_⟩
  have h1 := hz n
  rw [hN n le_rfl, LinearMap.mem_ker, map_sub, Q.ρ_self, Q.ρ_self, sub_eq_zero] at h1
  have h2 := hyx n le_rfl
  rw [Q.ρ_self] at h2
  rw [← h2]
  exact h1

theorem lim_cokernel_bounded : ∀ (W : Type) [CommRing W] [IsNoetherianRing W] (l : ℕ) (S S' : Sys.{1} W)
    (_ : LSeq l S S'), (∀ n, IsArtinian W (S.M n)) → Module.Finite W S'.lim →
    ∃ c : ℕ, ∀ n (x : S.M n), ∃ y : S.lim, y.1 n = ((l : W) ^ c) • x := by
  intro W _ _ l S S' Q hA hF
  obtain ⟨c, hc⟩ := pow_torsion_bounded ((l : W)) S'.lim
  refine ⟨c, fun n x => lift_of_conn_zero Q hA n _ (fun a => ?_)⟩
  have h0 : conn Q n ((l : W) ^ c • x) = 0 := by
    rw [← conn_smul]
    exact hc n _ (conn_kill Q n x)
  have h3 := congrArg (fun v : S'.lim => (v : ∀ m, S'.M m) a) h0
  simpa [conn] using h3

end GlobalTheory.CompanionTheory.TwCok
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundedCokernelLimitToLevelStatement

section

@[expose] public section

open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw

theorem _root_.GlobalTheory.T.bounded_cokernel_limit_to_level : ∀ (W : Type) [CommRing W] [IsNoetherianRing W] (l : ℕ) (S S' : Sys.{1} W) (_ : LSeq l S S'), (∀ n, IsArtinian W (S.M n)) → Module.Finite W S'.lim → ∃ c : ℕ, ∀ n (x : S.M n), ∃ y : S.lim, y.1 n = ((l : W) ^ c) • x := by
  first | exact @GlobalTheory.CompanionTheory.TwCok.lim_cokernel_bounded | exact GlobalTheory.CompanionTheory.TwCok.lim_cokernel_bounded | (intros; apply GlobalTheory.CompanionTheory.TwCok.lim_cokernel_bounded <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModuleFiniteLimitOfLseq

section

@[expose] public section

open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw

namespace GlobalTheory.CompanionTheory.TowerLim

theorem module_finite_lim : ∀ (W : Type) [CommRing W] (l : ℕ) [IsAdicComplete (Ideal.span {(l : W)}) W]
    (S S' : Sys.{1} W) (_ : LSeq l S S'), IsFiniteLength W (S.M 1) → Module.Finite W S.lim := by
  intro W _ l _ S S' L h1
  have hfl := GlobalTheory.T.finite_length_of_lseq_first W l S S' L h1
  have hart : ∀ n, IsArtinian W (S.M n) := fun n =>
    (isFiniteLength_iff_isNoetherian_isArtinian.1 (hfl n)).2
  have hinj := GlobalTheory.T.limit_divisible_of_vanishing_level W l S S' L hart

  have hvan : ∀ n, (Ideal.span {(l : W)} ^ n • (⊤ : Submodule W S.lim)) ≤ LinearMap.ker (pr S n) := by
    intro n
    refine Submodule.smul_le.2 fun r hr m _ => ?_
    rw [Ideal.span_singleton_pow] at hr
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [LinearMap.mem_ker, map_smul, mul_smul]
    rw [L.kill n, smul_zero]
  have hH : IsHausdorff (Ideal.span {(l : W)}) S.lim := by
    refine ⟨fun x hx => Subtype.ext (funext fun n => ?_)⟩
    have hm : x ∈ (Ideal.span {(l : W)} ^ n • (⊤ : Submodule W S.lim)) := by
      simpa [SModEq.zero] using hx n
    exact hvan n hm
  have hmem1 : ∀ x : S.lim, pr S 1 x = 0 → x ∈ Ideal.span {(l : W)} • (⊤ : Submodule W S.lim) := by
    intro x hx
    obtain ⟨y, hy⟩ := hinj 1 x hx
    rw [hy, pow_one]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) trivial
  have hle : Ideal.span {(l : W)} • (⊤ : Submodule W S.lim) ≤ LinearMap.ker (pr S 1) := by
    simpa using hvan 1
  let q := (Ideal.span {(l : W)} • (⊤ : Submodule W S.lim)).liftQ (pr S 1) hle
  have hq : Function.Injective q := by
    refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
    induction z using Submodule.Quotient.induction_on with
    | H x =>
      rw [Submodule.Quotient.mk_eq_zero]
      exact hmem1 x hz
  have : IsNoetherian W (S.M 1) := (isFiniteLength_iff_isNoetherian_isArtinian.1 h1).1
  have : Module.Finite W (S.lim ⧸ Ideal.span {(l : W)} • (⊤ : Submodule W S.lim)) :=
    Module.Finite.of_injective q hq
  obtain ⟨r, s, hs⟩ := Module.Finite.exists_fin (R := W)
    (M := S.lim ⧸ Ideal.span {(l : W)} • (⊤ : Submodule W S.lim))
  choose s' hs' using fun i => Submodule.Quotient.mk_surjective _ (s i)
  have : IsPrecomplete (Ideal.span {(l : W)}) (Fin r → W) := ReciprocityTheory.Coh.isPrecomplete_pi _
  have hsurj : Function.Surjective ((Ideal.span {(l : W)} • (⊤ : Submodule W S.lim)).mkQ ∘ₗ
      Fintype.linearCombination W s') := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hs, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨Pi.single i 1, by simp [hs']⟩
  exact Module.Finite.of_surjective _ (surjective_of_mkQ_comp_surjective hsurj)

end GlobalTheory.CompanionTheory.TowerLim
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModuleFiniteLimitOfLseqStatement

section

@[expose] public section

open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw

theorem _root_.GlobalTheory.T.module_finite_limit_of_lseq : ∀ (W : Type) [CommRing W] (l : ℕ) [IsAdicComplete (Ideal.span {(l : W)}) W] (S S' : Sys.{1} W) (_ : LSeq l S S'), IsFiniteLength W (S.M 1) → Module.Finite W S.lim := by
  first | exact @GlobalTheory.CompanionTheory.TowerLim.module_finite_lim | exact GlobalTheory.CompanionTheory.TowerLim.module_finite_lim | (intros; apply GlobalTheory.CompanionTheory.TowerLim.module_finite_lim <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.PhiAIter

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg

namespace CrystallineSemistableComparison.Pb



variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K)

def sT (M : Model l K) (j : ℕ) : Sys.{1} (AW r) := HMS r M j

def sH (M : Model l K) (j : ℕ) : Sys.{1} (AW r) := M.HS true j

def gH (M : Model l K) (j : ℕ) : Sys.Hom (HSW r M j) (sT r M j) (algebraMap (WittVector l r.k) (AW r)) :=
  ⟨fun n => bW r M n j, fun n y => bW_red r M n j y⟩

def ψA (N : ℕ) : AW r →+* AW r := Mid.phiA l N

variable {N : ℕ} (hT : Mid.TeichmullerCongruence r N)

def nuH (M : Model l K) (j : ℕ) : Sys.Hom (sH r M j) (sT r M j) (ψA r N) := ⟨fun n => Mid.nu r M n j hT, fun n x => nu_red r hT M n j x⟩

def muH (M : Model l K) (j : ℕ) : Sys.Hom (sT r M j) (sH r M j) (RingHom.id _) := ⟨fun n => Mid.mu r M n j hT, fun n x => mu_red r hT M n j x⟩

theorem lw_fin (M : Model l K) (hM : M.Sm) (j : ℕ) : Module.Finite (WittVector l r.k) (HSW r M j).lim := by
  obtain ⟨E⟩ := LsG.ls_seq r M hM j
  exact GlobalTheory.T.module_finite_limit_of_lseq _ l _ _ E (smooth_model_finite_length_link r M hM j)

theorem pin_all (M : Model l K) (j : ℕ) : ∃ (e : ℕ) (α : (sH r M j).lim →+ AW r ⊗[WittVector l r.k] (HSW r M j).lim),
    M.Sm → Fa.Pin l (gH r M j) (nuH r hT M j) e α := by
  by_cases hM : M.Sm
  swap
  · exact ⟨0, 0, fun h => absurd h hM⟩
  obtain ⟨E⟩ := LsG.ls_seq r M hM j
  have ha : ∀ n, IsArtinian (WittVector l r.k) ((HSW r M j).M n) := fun n =>
    (isFiniteLength_iff_isNoetherian_isArtinian.1 (GlobalTheory.T.finite_length_of_lseq_first _ l _ _ E (smooth_model_finite_length_link r M hM j) n)).2
  obtain ⟨c, hc⟩ := GlobalTheory.T.bounded_cokernel_limit_to_level _ l _ _ E ha (lw_fin r M hM (j + 1))
  have := flatW r
  have : IsAdicComplete (Ideal.span {(l : AW r)}) (AW r) := adicA
  obtain ⟨α, hα⟩ := Fa.pin_ex l (WittVector.irreducible l) c (lw_fin r M hM j) E.kill (GlobalTheory.T.limit_divisible_of_vanishing_level _ l _ _ E ha) hc (gH r M j)
    (bc_tens r M hM j) (nuH r hT M j)
  exact ⟨c, α, fun _ => hα⟩

theorem iter_lim {R : Type} [CommRing R] {S : Sys.{1} R} {σ : R →+* R} (φ : Sys.Hom S S σ) (N n : ℕ) (x : S.lim) :
    ((⇑φ.lim.toAddMonoidHom)^[N] x).1 n = (⇑(φ.f n))^[N] (x.1 n) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    rfl

def betaP (M : Model l K) (j : ℕ) : AL r M j →ₗ[(per l K).A] HL M j where
  toFun w := Fa.beta (A := AW r) (gH r M j) (muH r hT M j) w
  map_add' := (Fa.beta (A := AW r) (gH r M j) (muH r hT M j)).map_add
  map_smul' a w := (Fa.beta (A := AW r) (gH r M j) (muH r hT M j)).map_smul (ofA r a) w

theorem phiA_iter (N : ℕ) (a : Acris l) :
    Mid.phiA l N a = (ACris.phi (K := ℂ_[l]) (p := l))^[N] a := by
  induction N with
  | zero => rfl
  | succ N ih => rw [Mid.phiA_succ, Function.iterate_succ_apply', ih]

def φA : AW r →+* AW r := ACris.phi (K := ℂ_[l]) (p := l)

def σA (σ : Gal(PadicAlgCl l/K)) : AW r →+* AW r := ACris.galCris σ

def Pinned (F : Fac r N) : Prop := ∀ M : Model l K, M.Sm → ∀ j, Fa.Pin l (gH r M j) (nuH r hT M j) (F.e M j) (F.α M j) ∧
  ∀ w, F.β M j w = Fa.beta (gH r M j) (muH r hT M j) w

def MuNu : Prop := ∀ (M : Model l K) (n j : ℕ) (x : B.Hc (B.schFn M.p) (okToOC l K) true n j),
  Mid.mu r M n j hT (Mid.nu r M n j hT x) = (⇑(B.phiHc (B.schFn M.p) (okToOC l K) n j))^[N] x

theorem fac_ex (hmn : MuNu r hT)
    (hφ : ∀ w, ACris.phi (K := ℂ_[l]) (p := l) (r.w w) = r.w (WittVector.frobenius w))
    (hσ : ∀ (g : K.fixingSubgroup) w, ACris.galCris (IntermediateField.fixingSubgroupEquiv K g) (r.w w) = r.w w) :
    ∃ F : Fac r N, Pinned r hT F := by
  choose e α h using pin_all r hT
  refine ⟨{ e := e
            α := α
            β := betaP r hT
            phiT := fun M j => Fa.tmap (A := AW r) (φA r) (Wc.phiS l (B.schFn M.p) r.ρ j).lim hφ
            galT := fun M j g => Fa.tmap (A := AW r) (σA r (IntermediateField.fixingSubgroupEquiv K g)) (τW := RingHom.id _) LinearMap.id (hσ g)
            phiT_tmul := fun _ _ _ _ _ => rfl
            galT_tmul := fun _ _ _ _ _ _ => rfl
            lin := ?_, fac := ?_, phi := ?_, gal := ?_, galβ := ?_, nat := ?_ }, fun M hM j => ⟨h M j hM, fun _ => rfl⟩⟩
  · intro M hM j a x
    exact ((h M j hM).lin a x).trans (congrArg (fun b : AW r => b • α M j x) (phiA_iter N a))
  · intro M hM j x
    exact (h M j hM).fac (muH r hT M j) x _ fun n => (hmn M n j _).trans (iter_lim (M.phiH j) N n x).symm
  · intro M hM j x
    exact ((h M j hM).op (h M j hM) (τ := φA r) (fun n => phiM r M n j) (Wc.phiS l (B.schFn M.p) r.ρ j).lim
      (fun n y => (bW_phi r M n j _).symm) _ (fun _ _ => rfl) x (phiL M j x) fun n => nu_phi r hT M n j _).2 rfl
  · intro M hM j g x
    exact ((h M j hM).op (h M j hM) (τ := σA r (IntermediateField.fixingSubgroupEquiv K g)) (fun n => galM r M _ (hσ g) n j) id
      (fun n y => (bW_gal r M _ (hσ g) n j _).symm) _ (fun _ _ => rfl) x (galL M j g x) fun n => nu_gal r hT M _ (hσ g) n j _).2 rfl
  · intro M hM j g y
    refine Subtype.ext (funext fun n => (mu_gal r hT M _ (hσ g) n j _).trans (congrArg (Mid.mu r M n j hT) ?_))
    have e1 : Fa.E (gH r M j) n ((1 : AW r) ⊗ₜ y) = bW r M n j (y.1 n) := (Fa.E_tmul _ n 1 y).trans (one_smul _ _)
    exact (congrArg (galM r M _ (hσ g) n j) e1).trans ((bW_gal r M _ (hσ g) n j _).trans e1.symm)
  · intro M M' u hu hM hM' j x
    refine ⟨0, ?_⟩
    rw [pow_zero, one_smul, sub_eq_zero]
    exact ((h M' j hM').op (h M j hM) (τ := RingHom.id _) (fun n => pullM r u hu n j) (Wc.pullS l r.ρ (B.schMap u hu) j).lim
      (fun n y => (bW_pull r u hu n j _).symm) (LinearMap.lTensor (AW r) (Wc.pullS l r.ρ (B.schMap u hu) j).lim).toAddMonoidHom
      (fun _ _ => rfl) x (pullL u hu j x) fun n => nu_pull r hT u hu n j _).1

end CrystallineSemistableComparison.Pb
end
end
end
