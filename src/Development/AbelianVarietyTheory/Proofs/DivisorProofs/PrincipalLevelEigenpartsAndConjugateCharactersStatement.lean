module

public import Development.AbelianVarietyTheory.Definitions.Divisors.OfCore
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePartBase
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilGramSignature
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGalConjEta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfUnitaryTensorIdeles
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeKeepsAndCommutes
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.UnitaryNorms.CharHost
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemNotMem
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfRegularForms
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurComponentsSpan
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotentsStatement
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceOffLevelSetProperties

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult Formalism.IndefR.Links GlobalTheory.SphPar
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory


open SplitOffPlaces Formalism.L2.Col Formalism.HermitianLatticesTheory in
theorem offS_not_type_places : ∀ {D : D7} (Pb : Formalism.L2.Host.PiBar D.host) (Pg : Finset (HeightOneSpectrum (𝓞 D.host.E))) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (P : HeightOneSpectrum (𝓞 D.host.E)), (∀ PP, PP ∈ Pg ↔ ∃ k, Pb.Div k PP) → (∀ PP ∈ Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ S) → OffS D S P → ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ ∀ PP ∈ Pg, PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P := by
  intro D Pb Pg S P hPg hS hP
  have key : ∀ PP ∈ Pg, PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P := by
    intro PP h
    obtain ⟨x, hx, hxP⟩ := hP _ (hS PP h)
    have hx' : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ PP.asIdeal := hx
    refine ⟨fun e => hxP _ rfl (e ▸ hx'), fun hc => ?_⟩
    obtain ⟨c', h1, h2⟩ := hc _ hx'
    refine hxP c' ?_ h1
    rw [h2]
    exact (D.sp.cm.fixed _).2 ⟨(x : D.host.F), rfl⟩
  have hne : ∀ PP ∈ Pg, PP ≠ P := fun PP h => (key PP h).1
  have hne' : ∀ PP ∈ Pg, PP ≠ conjSpec P := by
    intro PP h e
    apply (key PP h).2
    intro c hc
    rw [e] at hc
    exact ⟨cO D.host.E c, hc, rfl⟩
  have hg : ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro k hk
    have h1 : Pb.pb k ≠ P.under (𝓞 D.host.K) := fun e => hne P ((hPg P).2 ⟨k, e.symm⟩) rfl
    have h2 : Pb.pb k ≠ (conjSpec P).under (𝓞 D.host.K) := fun e =>
      hne' (conjSpec P) ((hPg _).2 ⟨k, e.symm⟩) rfl
    obtain ⟨x, hx, hx1, hx2⟩ := exists_mem_not_mem h1 h2
    obtain ⟨x', n, hx', hn⟩ := exists_norm D x
    have hnP : (n : 𝓞 D.host.E) ∉ P.asIdeal := by
      intro h
      have e : (n : 𝓞 D.host.E) = algebraMap (𝓞 D.host.K) (𝓞 D.host.E) x * cO D.host.E (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) x) := by
        rw [← hx', ← map_mul, hn, map_intCast]
      rw [e] at h
      rcases P.isPrime.mem_or_mem h with h | h
      · exact hx1 h
      · exact hx2 h
    have hnb : (n : 𝓞 D.host.K) ∈ (Pb.pb k).asIdeal := hn ▸ Ideal.mul_mem_right _ _ hx
    have hp : Prime (D.host.g k : ℤ) := Nat.prime_iff_prime_int.1 (D.host.g_prime k)
    by_cases hd : (D.host.g k : ℤ) ∣ n
    · obtain ⟨m, rfl⟩ := hd
      apply hnP
      push_cast
      exact Ideal.mul_mem_right _ _ hk
    · obtain ⟨a, b, hab⟩ := (hp.irreducible.coprime_iff_not_dvd).2 hd
      apply (Pb.pb k).isPrime.ne_top
      rw [Ideal.eq_top_iff_one]
      have e : (1 : 𝓞 D.host.K) = a * ((D.host.g k : ℕ) : 𝓞 D.host.K) + b * n := by
        exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 D.host.K) hab.symm
      rw [e]
      exact add_mem (Ideal.mul_mem_left _ _ (Pb.pb_over k)) (Ideal.mul_mem_left _ _ hnb)
  refine ⟨?_, key⟩
  intro h
  rw [Nat.cast_mul] at h
  rcases P.isPrime.mem_or_mem h with h | h
  · exact hg 0 h
  · exact hg 1 h

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalOperatorCommuteLevelFiniteGroup

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev
open scoped TensorProduct

namespace GlobalTheory.HeckeKeepsGood

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

variable {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank}

theorem levChi_mul {k k' : GA D V} (hk : k ∈ levG V β L) (hk' : k' ∈ levG V β L) :
    levChi V β L (k * k') = levChi V β L k * levChi V β L k' := by
  unfold levChi
  rw [← Units.val_mul, MonoidHom.map_mul]
  exact congrArg Units.val ((Formalism.L2.DIV.levChar D.sp.cm V.gram β L).map_mul ⟨_, hk.2⟩ ⟨_, hk'.2⟩)

variable {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ}
  {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))} {P : HeightOneSpectrum (𝓞 D.host.E)} {d : List ℤ} {R : Finset (GA D V)}

theorem hasType_heckeLin (hB : IsBaseFrame V β Λ N) (hN : ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    (hPP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ IsConjPl PP P)
    (hR : Hecke₂ V (levG V β L : Set (GA D V)) (levChi V β L) Sb P d R) {F : GA D V → ℂ}
    (hF : HasType V β L F) : HasType V β L (heckeLin V R F) :=
  GlobalTheory.SphericalOps.level_heckeLin (fun _ hk _ hk' => levChi_mul hk hk')
    (fun e f _ hI => ((GlobalTheory.LevSplit.lev_split V β Λ N L hB).2 P e f hI hN hPP).2.2) hR hF

theorem sphericalOperator_commute_levelFiniteGroup (hB : IsBaseFrame V β Λ N) (hN : ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    (hPP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ IsConjPl PP P)
    (hR : Hecke₂ V (levG V β L : Set (GA D V)) (levChi V β L) Sb P d R) {F : GA D V → ℂ}
    (hF : HasType V β L F) (x : Formalism.L2.DIV.G0 L.Pg L.r) :
    actG0 V β L x (heckeLin V R F) = heckeLin V R (actG0 V β L x F) := by
  have hG := hasType_heckeLin hB hN hPP hR hF
  obtain ⟨e, f, ϖ, α, -, hI, -, -, -, hJ, hχ, -, -, hRs, -⟩ := hR
  unfold actG0
  split_ifs with hk
  swap
  · exact (map_zero _).symm
  have hκ := hk.choose_spec
  generalize hk.choose = κ at hκ ⊢
  obtain ⟨a1, -, a3⟩ := (GlobalTheory.LevSplit.lev_split V β Λ N (flagL L) hB).2 P e f hI hN hPP
  obtain ⟨k₁, m₁, k₂, -, s₁, s₂, rfl⟩ := a3 κ ⟨hκ.1, hκ.2.1, Subgroup.mem_top _⟩
  have m : k₁ ∈ levG V β L := (hJ k₁ s₁).2 ((a1 k₁ s₁).1 m₁)
  obtain ⟨hff, hcf, -⟩ := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e f hI
  have hc : ∀ a, SuppF V f a → Commute a k₂ := fun a ha =>
    ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).1 f hff hcf).2.2 (1 - f) a k₂ (by rw [mul_sub, mul_one, hff, sub_self]) ha s₂
  have key : ∀ G : GA D V → ℂ, HasType V β L G → ∀ h, G (h * (k₁ * k₂)) = G (h * k₂) := fun G hG h => by
    rw [(hc k₁ s₁).eq, ← mul_assoc, hG k₁ m, hχ k₁ m s₁, one_mul]
  funext h
  rw [key _ hG]
  show _ * ∑ γ ∈ R, F (h * k₂ * γ) = ∑ γ ∈ R, _ * F (h * γ * (k₁ * k₂))
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ hγ => ?_
  rw [key F hF, mul_assoc h γ, (hc γ (hRs γ hγ)).eq, mul_assoc h]

end GlobalTheory.HeckeKeepsGood
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelEigenpartsAndConjugateCharacters

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
open GlobalTheory.LiftLower
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PrincipalDecomp

open GlobalTheory.SphericalOps GlobalTheory.HeckeAdjoint GlobalTheory.HeckeOrthSum

theorem iSup_partH_eq_top_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), SchurMult R.θ (R.MW i σ) (levSW R i) (chiW R i) (R.νW i) (R.fdW i) → (⨆ (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) (_ : IsNormSys R i c), partH R i σ c) = ⊤ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i σ hS
  classical
  obtain ⟨hinj, hrange, -⟩ := hC.models.HW i σ
  have hrange' : LinearMap.range (R.HW i σ).e =
      Mult R.θ (R.MW i σ) (Lev.levG _ (R.βW i) (R.datWp i R.triv) : Set (GA D (Wc D i))) (chiW R i) := hrange
  haveI : FiniteDimensional ℂ
      (Mult R.θ (R.MW i σ) (Lev.levG _ (R.βW i) (R.datWp i R.triv) : Set (GA D (Wc D i))) (chiW R i)) := by
    rw [← hrange']; infer_instance
  obtain ⟨n, hB⟩ := hC.lev.βW i
  have key := mult_le_of_parts (J := Lev.levG _ (R.βW i) (R.datWp i R.triv)) (Sb := GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF R)
    hC.models.inf (hC.models.νW i).1.1 (hC.models.νW i).2 hS (fun P d Rp h T hT => ?_)
    ((⨆ (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) (_ : IsNormSys R i c), partH R i σ c).map (R.HW i σ).e) (fun c hc T hT => ?_)
  · rw [eq_top_iff]
    intro x _
    obtain ⟨y, hy, e⟩ := key (hrange' ▸ LinearMap.mem_range_self _ x)
    exact hinj e ▸ hy
  · have hN : (((1 ^ n : ℕ) : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
      rw [one_pow, Nat.cast_one]
      exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
    have hO : OffS D (GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF R) P := by
      obtain ⟨_, _, _, _, hO, -⟩ := h
      exact hO
    have hP : ∀ PP, PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ (R.datWp i R.triv).Q → PP ≠ P ∧ ¬ Lev.IsConjPl PP P := by
      rintro PP (hP | hP)
      · exact GlobalTheory.HeckeOffLevel.sep_of_offS hO (by
          unfold GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF
          exact Finset.mem_image.2 ⟨PP, hP, rfl⟩)
      · exact absurd hP (Finset.notMem_empty _)
    rw [GlobalTheory.MultMem.mem_mult_iff] at hT ⊢
    refine isMultMap_heckeOn hT (fun k hk => ?_) fun v => GlobalTheory.HeckeOffLevel.hasType_heckeLin hB hN hP h (hT.lev v)
    obtain ⟨_, _, _, _, -, -, -, -, -, -, -, -, -, -, hc⟩ := h
    exact (hc.1 k hk).1
  · obtain ⟨y, rfl⟩ : T ∈ LinearMap.range (R.HW i σ).e := hrange' ▸ hT.1
    exact Submodule.mem_map_of_mem
      (le_iSup₂_of_le (f := fun (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) (_ : IsNormSys R i c) => partH R i σ c) c hc le_rfl hT)

end GlobalTheory.PrincipalDecomp

namespace GlobalTheory.LiftLower

theorem gW_mem_partH_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) (g : G), ∀ x ∈ partH R i σ c, R.gW i σ g x ∈ partH R i σ c := by
  classical
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i σ c g x hx
  unfold partH at hx ⊢
  rw [Submodule.mem_comap, mem_partFull] at hx ⊢
  refine ⟨?_, fun P d Rp hR v => ?_⟩
  · have h : (R.HW i σ).e (R.gW i σ g x) ∈ LinearMap.range (R.HW i σ).e := LinearMap.mem_range_self _ _
    rw [(hC.models.HW i σ).2.1] at h
    exact h
  have hO : OffS D (GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF R) P := by
    obtain ⟨_, _, _, _, h, -⟩ := hR
    exact h
  obtain ⟨-, h2⟩ := GlobalTheory.offS_not_type_places R.C.P R.Pg (GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF R) P hC.lev.Pg
    (fun PP hPP => by unfold GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF; exact Finset.mem_image.2 ⟨PP, hPP, rfl⟩) hO
  obtain ⟨a, hB⟩ := hC.lev.βW i
  have hN : (((1 ^ a : ℕ)) : 𝓞 D.host.E) ∉ P.asIdeal := fun h =>
    P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using h))
  have hPP : ∀ PP, PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ (R.datWp i R.triv).Q → PP ≠ P ∧ ¬ Lev.IsConjPl PP P := by
    rintro PP (h | h)
    · exact h2 PP h
    · exact absurd h (Finset.notMem_empty _)
  have hT := ((GlobalTheory.MultMem.mem_mult_iff ..).1 hx.1).lev v
  rw [hC.models.gW i σ g x, postOn_apply, ← map_smul, ← hx.2 P d Rp hR v]
  exact (GlobalTheory.HeckeKeepsGood.sphericalOperator_commute_levelFiniteGroup hB hN hPP hR hT (R.eG g)).symm

end GlobalTheory.LiftLower

namespace GlobalTheory.ConjMuChar

theorem exists_galConj_chrEq_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s → ∀ μ' : (AE D)ˣ →* Circle, ChiAt R i σ μ' → ∃ μH : Formalism.L2.Host.HChar D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsGalConj s 0 (R.C.mu0 i * R.xiH A.μ0) μH ∧ ChrEq μ' μH := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i σ s hσ μ' hμ
  obtain ⟨μH, hH⟩ := GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D μ' hμ.1
  refine ⟨μH, fun P k => ?_, hH⟩
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, hinf, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  have hx : infPart D ((Formalism.L2.JoinChr.locU he.1 k : (AE D)ˣ) : AE D) = 1 := by
    rw [Formalism.L2.JoinChr.locU_val, Formalism.L2.JoinChr.locE, RingHom.map_add (f := _), RingHom.map_mul, hinf, zero_mul, add_zero,
      RingHom.map_one]
  obtain ⟨y, hy0, hy⟩ := hμ.2.2.2.1 _ hx
  have a1 := hH.2 P e he k _ (Formalism.L2.JoinChr.locU_val he.1 k)
  have a2 := (hC.lev.mu0 i).2 P e he k _ (Formalism.L2.JoinChr.locU_val he.1 k)
  rw [hC.lev.xi_base, mul_one]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.twVal
  simp only [Complex.ofReal_zero, zero_mul, neg_zero, Complex.cpow_zero, mul_one]
  rw [← a1, ← a2, hy, hy0, hσ.1]

end GlobalTheory.ConjMuChar

namespace GlobalTheory.EtaConjChar

open Formalism.L2.Host Formalism.L2.JoinChr

theorem exists_galConj_eta_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s → ∀ η' : (AE D)ˣ →* Circle, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsEtaConj σ R.eta η' → ∃ ηH : Formalism.L2.Host.HChar D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsGalConj s (1 / 2) R.C.eta ηH ∧ ChrEq η' ηH := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR σ s hσ η' hη
  obtain ⟨ηH, hH⟩ := GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D η' hη.1
  refine ⟨ηH, fun P k => ?_, hH⟩
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  obtain ⟨y, hy1, hy2⟩ := hη.2.2 P e he (locU he.1 (unif P)) rfl
  have h0 : ∀ u : D.host.Eˣ, P.valuation D.host.E (u : D.host.E) = 1 → R.C.eta.locK P u = 1 := fun u hu =>
    R.C.isEta.unr P _ ((P.valuedAdicCompletion_eq_valuation' (u : D.host.E)).trans hu)
  rw [twVal_half _ P (locK_eq_one hH hη.2.1 P), twVal_half _ P h0, map_zpow₀,
    ← hH.2 P e he _ (locU he.1 (unif P)) rfl, ← hR.lev.eta.2 P e he _ (locU he.1 (unif P)) rfl, ← hy1, ← hy2, hσ.1]

end GlobalTheory.EtaConjChar

namespace GlobalTheory.FiveClauseParts

theorem parts_conj_five : (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), SchurMult R.θ (R.MW i σ) (levSW R i) (chiW R i) (R.νW i) (R.fdW i) → (⨆ (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) (_ : IsNormSys R i c), partH R i σ c) = ⊤) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) (g : G), ∀ x ∈ partH R i σ c, R.gW i σ g x ∈ partH R i σ c) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s → ∀ μ' : (AE D)ˣ →* Circle, ChiAt R i σ μ' → ∃ μH : Formalism.L2.Host.HChar D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsGalConj s 0 (R.C.mu0 i * R.xiH A.μ0) μH ∧ ChrEq μ' μH) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s → ∀ η' : (AE D)ˣ →* Circle, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsEtaConj σ R.eta η' → ∃ ηH : Formalism.L2.Host.HChar D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsGalConj s (1 / 2) R.C.eta ηH ∧ ChrEq η' ηH) :=
  ⟨GlobalTheory.PrincipalDecomp.iSup_partH_eq_top_five, GlobalTheory.LiftLower.gW_mem_partH_five,
    GlobalTheory.ConjMuChar.exists_galConj_chrEq_five, GlobalTheory.EtaConjChar.exists_galConj_eta_five⟩

end GlobalTheory.FiveClauseParts

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelEigenpartsAndConjugateCharactersStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
open GlobalTheory.LiftLower
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.principalLevel_eigenparts_and_conjugate_characters : (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), SchurMult R.θ (R.MW i σ) (levSW R i) (chiW R i) (R.νW i) (R.fdW i) → (⨆ (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) (_ : IsNormSys R i c), partH R i σ c) = ⊤) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) (g : G), ∀ x ∈ partH R i σ c, R.gW i σ g x ∈ partH R i σ c) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s → ∀ μ' : (AE D)ˣ →* Circle, ChiAt R i σ μ' → ∃ μH : Formalism.L2.Host.HChar D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsGalConj s 0 (R.C.mu0 i * R.xiH A.μ0) μH ∧ ChrEq μ' μH) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s → ∀ η' : (AE D)ˣ →* Circle, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsEtaConj σ R.eta η' → ∃ ηH : Formalism.L2.Host.HChar D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsGalConj s (1 / 2) R.C.eta ηH ∧ ChrEq η' ηH) := by
  first | exact @GlobalTheory.FiveClauseParts.parts_conj_five | exact GlobalTheory.FiveClauseParts.parts_conj_five | (intros; apply GlobalTheory.FiveClauseParts.parts_conj_five <;> assumption)
end
end
