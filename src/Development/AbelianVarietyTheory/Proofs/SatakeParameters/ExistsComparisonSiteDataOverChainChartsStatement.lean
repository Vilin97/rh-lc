module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingYAlt
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BaseLatticeSelfDualOfLocalEq
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ChiFinOfGlevH
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUnifPow
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
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
import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MemberChainFormsLevelPrimeEqMember
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSDLatLatK
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.IntSplitOf
import Formalism.LocalToGlobal.HermitianForms.BothLemmas
import Mathlib.Tactic.Linter.Style
public import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaSeriesDataHypothesesBelowMaximalLevel
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChiRatAllOfAdTie

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwUChiRat

open GlobalTheory.TwU Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG NumberField IsDedekindDomain

section Gen

variable {D : D7} {X : Fields} (s : Seam D X) {i : ℕ} {hi : i ≤ D.R.m} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
  (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T D.R.f bad) {SB : Finset (HeightOneSpectrum (𝓞 X.E))}
  (fb : SB → GL (Fin (D.R.N i)) D.host.E) (dep : SB → ℕ)
  (Rel : SB → (Sp X.E (D.R.N i) ≃ₗ[X.E] Sp X.E (D.R.N i)) → X.K → Prop)

theorem exists_isOver (Q : HeightOneSpectrum (𝓞 D.host.E)) : ∃ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v Q := by
  refine ⟨⟨Q.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)), Ideal.comap_isPrime _ _, ?_⟩, rfl⟩
  intro h
  have hN : ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 D.host.F) ∈ Q.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := by
    rw [Ideal.mem_comap, map_natCast]; exact Ideal.absNorm_mem _
  rw [h, Ideal.mem_bot] at hN
  have : Ideal.absNorm Q.asIdeal = 0 := by exact_mod_cast hN
  exact Q.ne_bot (Ideal.absNorm_eq_zero_iff.1 this)

theorem chiRatAll_of_le (hLe : LocLe s lev fb dep Rel) (hChi : ChiIs s lev fb dep Rel)
    (hK : ∀ y : X.K, ∃ k : D.what₂.LL, D.what₂.embLL k = s.σ₀ y) : ChiRatAll lev D.what₂.embLL := by
  classical
  intro κ
  have hv : ∀ P : SB, ∃ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v (seamP s P.1) := fun P => exists_isOver (seamP s P.1)
  choose v hv using hv
  have hU := (lev.U_eq κ.1).1 κ.2
  have hgz : ∀ P : SB, ∃ g z, Rel P g z ∧ InFrame s fb dep P κ.1 g := fun P => hLe P (v P) (hv P) κ.1 hU.1 (hU.2 (v P))
  choose g z hgz using hgz
  have h1 := hChi κ g z hgz
  obtain ⟨k, hk⟩ := hK (∏ P, z P)
  refine ⟨k⁻¹, ?_⟩
  rw [map_inv₀, hk]
  exact (eq_inv_of_mul_eq_one_left h1).symm

end Gen

theorem chiRatAll_of_adTie : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (St : GlobalTheory.TwU.ChainCharts D u μ) (A : GlobalTheory.TwU.AdData t u μ St) (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt) (a : 𝓞 D.host.E), GlobalTheory.TwU.AdTie A dtU a → (∀ y : t.X.K, ∃ k : D.what₂.LL, D.what₂.embLL k = t.seam.σ₀ y) → ∀ i hi β, ChiRatAll ((St i hi).K β).lev D.what₂.embLL := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ St A dtU a H hK i hi β
  have hm := m_eq t μ
  rcases Nat.lt_or_ge t.m2 i with h | h
  · rcases Nat.lt_or_ge (t.m2 + 1) i with h' | h'
    · obtain rfl : i = t.m2 + 1 + 1 := by omega
      exact chiRatAll_of_le t.seam _ _ _ _ (H.levTop β).1 (H.levTop β).2 hK
    · obtain rfl : i = t.m2 + 1 := by omega
      exact chiRatAll_of_le t.seam _ _ _ _ (H.levCpl β).1 (H.levCpl β).2.2 hK
  · have hlt : i < D.R.m := by omega
    exact chiRatAll_of_le t.seam _ _ _ _ (H.levMid i hlt h β).1 (H.levMid i hlt h β).2.2 hK

end GlobalTheory.TwUChiRat
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvCoordsIsBasisAtBaseLatticeOfStdCompanion

section

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseAtCompan

theorem mem_reL_symm {E : Type} [Field E] [NumberField E] {a b : ℕ} (h : a = b) (L : Submodule (𝓞 E) (Fin b → E))
    (x : Fin a → E) : x ∈ reL h.symm L ↔ reV h E x ∈ L := by
  subst h
  show x ∈ reL rfl L ↔ reV rfl E x ∈ L
  rw [reL_rfl, reV_rfl]

theorem mem_mvL_iff {E : Type} [Field E] [NumberField E] {N : ℕ} (co : GL (Fin N) E) (Λ : Submodule (𝓞 E) (Fin N → E))
    (y : Fin N → E) : (co : Matrix (Fin N) (Fin N) E) *ᵥ y ∈ mvL co Λ ↔ y ∈ Λ := by
  constructor
  · rintro ⟨z, hz, e⟩
    have e' : toLE co z = toLE co y := e
    rwa [(toLE co).injective e'] at hz
  · intro hy
    exact ⟨y, hy, rfl⟩

theorem smul_mem_of_mem_compan {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    {R : Ranks} (sp : Spaces R F E) {σ : E →ₐ[F] E} (hσ : (σ : E →+* E) = (sp.cm.sig : E →+* E)) {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E σ J T f bad) (a : 𝓞 E)
    (y : Fin n → E) (hy : y ∈ compan (sp := sp) J a S.Lb) : (T : E) • y ∈ S.Lb := by
  let M : Submodule (𝓞 E) (Fin n → E) :=
    { carrier := {y | (T : E) • y ∈ S.Lb}
      add_mem' := fun {x z} hx hz => by
        show (T : E) • (x + z) ∈ S.Lb
        rw [smul_add]; exact add_mem hx hz
      zero_mem' := by show (T : E) • (0 : Fin n → E) ∈ S.Lb; rw [smul_zero]; exact zero_mem _
      smul_mem' := fun c x hx => by
        show (T : E) • (c • x) ∈ S.Lb
        rw [smul_comm]; exact S.Lb.smul_mem c hx }
  have hd : Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J S.Lb) ≤ M := by
    rw [Submodule.span_le]
    intro z hz
    rw [← hσ] at hz
    exact S.Lb_dual z hz
  have hL : S.Lb ≤ Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J S.Lb) := by
    intro x hx
    apply Submodule.subset_span
    have := S.Lb_int x hx
    rwa [hσ] at this
  exact hd (sup_le hL Submodule.smul_le_right hy)

theorem isBaseAt_inv_of_latCo : ∀ {D : D7} (X0 : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {i : ℕ} (hi : i + 1 ≤ D.R.m) {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (S : StepLevel D.host.F D.host.E (sigD D) (gramN D (i + 1) hi) T D.R.f bad) (co : GL (Fin (D.R.N (i + 1))) D.host.E) (a : 𝓞 D.host.E), ¬ (D.what₂.places.resChar w) ∣ T → GlobalTheory.TwU.latCo D.sp (gramN D (i + 1) hi) co a 1 S.Lb = StandardLatticesGL3.stdL D (D.R.N (i + 1)) → IsBaseAt X0 u w hg ((Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E).symm co⁻¹) (reL (rankN D (i + 1) hi).symm S.Lb) := by
  intro D X0 u w hg i hi T bad S co a hT hstd
  have hr := rankN D (i + 1) hi
  set C := compan (sp := D.sp) (gramN D (i + 1) hi) a S.Lb with hC
  have h1 : latAd (1 : GL (Fin (D.R.N (i + 1))) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) S.Lb = S.Lb := by
    rw [GlobalTheory.SDCompan.latAd_eq]
    exact Formalism.L2.GlobalTheoryTheory.Comp.glob_one ⟨S.Lb_fin, S.Lb_span⟩
  have hm : mvL co C = StandardLatticesGL3.stdL D (D.R.N (i + 1)) := by
    rw [← hstd, GlobalTheory.TwU.latCo, h1]
  have hCi : ∀ y, y ∈ C ↔ ∀ k, ((co : Matrix (Fin (D.R.N (i + 1))) (Fin (D.R.N (i + 1))) D.host.E) *ᵥ y) k ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
    intro y
    rw [← mem_mvL_iff co C y, hm]
    unfold StandardLatticesGL3.stdL
    rw [Submodule.mem_pi]
    simp only [Set.mem_univ, true_imp_iff, Submodule.mem_one, RingHom.mem_range]
  have hTC : ∀ y ∈ C, (T : D.host.E) • y ∈ S.Lb :=
    smul_mem_of_mem_compan D.sp rfl S a
  refine IsBaseAt.congr X0 u w hg (isBaseAt_free X0 u w hg _ (reL (rankN D (i + 1) hi).symm C) fun x => ?_) fun w' hw => ?_
  · rw [mem_reL_symm, hCi]
    exact free_re (rankN D (i + 1) hi) co _ x
  · have hT' : ((T : ℕ) : 𝓞 D.host.F) ∉ w'.asIdeal :=
      natCast_notMem w' (D.what₂.places.resChar_prime w) hw hT
    refine (loc_lattice_eq_of_torsion_away w' _ _ T hT' ?_ ?_).symm
    · intro x hx
      rw [mem_reL_symm hr] at hx ⊢
      exact le_sup_left (a := S.Lb) hx
    · intro y hy
      rw [mem_reL_symm hr] at hy ⊢
      rw [map_smul]
      exact hTC _ hy

end GlobalTheory.BaseAtCompan
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvCoordsIsBasisAtBaseLatticeOfStdCompanionStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.inv_coords_isBasisAt_baseLattice_of_std_companion : ∀ {D : D7} (X0 : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {i : ℕ} (hi : i + 1 ≤ D.R.m) {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (S : StepLevel D.host.F D.host.E (sigD D) (gramN D (i + 1) hi) T D.R.f bad) (co : GL (Fin (D.R.N (i + 1))) D.host.E) (a : 𝓞 D.host.E), ¬ (D.what₂.places.resChar w) ∣ T → GlobalTheory.TwU.latCo D.sp (gramN D (i + 1) hi) co a 1 S.Lb = StandardLatticesGL3.stdL D (D.R.N (i + 1)) → IsBaseAt X0 u w hg ((Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E).symm co⁻¹) (reL (rankN D (i + 1) hi).symm S.Lb) := by
  first | exact @GlobalTheory.BaseAtCompan.isBaseAt_inv_of_latCo | exact GlobalTheory.BaseAtCompan.isBaseAt_inv_of_latCo | (intros; apply GlobalTheory.BaseAtCompan.isBaseAt_inv_of_latCo <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsFractionRingGat

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ggeo.FracLocal

theorem isFractionRing_gat : ∀ {D : D7} (Gl : G.LatInst D) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), IsFractionRing (D.gat u w hg).O (D.gat u w hg).Kf :=
  fun {_} Gl u w hg => GlobalTheory.TwV.Lt.fracAt Gl u w hg

end GlobalTheory.Ggeo.FracLocal
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotMemUnderSBOfGIdx

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU

theorem not_mem_underSB_of_gIdx : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (μ : D.what₂.Tup), (D.what₂.places.resChar w) ∉ Dx.Qp μ → ∀ v, GlobalTheory.TwU.UnderSB t μ v → ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal := by
  intro D L hT Gi Gl Kc Dx cX ex t u w hg μ hQ v hv hmem
  classical
  obtain ⟨P, hP, hvP⟩ := hv
  have h1 : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.E) ∈ (seamP t.seam P).asIdeal := by
    have h0 : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈
        (seamP t.seam P).asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := hvP ▸ hmem
    rw [Ideal.mem_comap, map_natCast] at h0
    exact h0
  have h2 : ((D.what₂.places.resChar w : ℕ) : 𝓞 t.X.E) ∈ P.asIdeal := by
    rw [← mem_seamP t.seam P, map_natCast]
    exact h1
  rcases Finset.mem_union.1 hP with hG | hQE
  · obtain ⟨k, hk⟩ : ∃ k, P ∈ t.Pr.vG k := by
      rcases Finset.mem_union.1 hG with h | h
      exacts [⟨0, h⟩, ⟨1, h⟩]
    have hgk : ((t.Pr.g k : ℕ) : 𝓞 t.X.E) ∈ P.asIdeal := by
      rw [← t.pr_ok.vG_norm k P hk]
      exact Ideal.absNorm_mem P.asIdeal
    have hnd : ¬ D.what₂.places.resChar w ∣ t.Pr.g k := by
      rw [t.g_rec]
      intro hd
      exact hg.2.2.2.2.1 (((Nat.prime_dvd_prime_iff_eq hg.1 (D.host.g_prime k)).1 hd) ▸ D.host.g_level k)
    have hc : IsCoprime ((D.what₂.places.resChar w : ℕ) : ℤ) ((t.Pr.g k : ℕ) : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hg.1).2 hnd)
    obtain ⟨a, b, hab⟩ := hc.map (Int.castRingHom (𝓞 t.X.E))
    have hone : (1 : 𝓞 t.X.E) ∈ P.asIdeal := by
      rw [← hab]
      refine P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ ?_) (P.asIdeal.mul_mem_left _ ?_)
      · simpa using h2
      · simpa using hgk
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hone)
  · exact hQ ((t.Q_rec μ _).2 ⟨hg.1, P, hQE, h2⟩)

end GlobalTheory.TwU
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsComparisonSiteDataOverChainCharts

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SiteEx



theorem siteD_exists : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (μ : D.what₂.Tup) (J : JIn t u μ), (D.what₂.places.resChar w) ∉ Dx.Qp μ → ∃ Z : SiteD J.Gd.herm u w hg (ex.tw.fm u μ), Z.Fo = foOf J.Hh J.St J.val ∧ SiteGood Z ∧ SiteRest Z ex.cmp ∧ ∀ i hi, Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E (Z.S i hi).B = (J.A.crd (i + 1) hi)⁻¹ := by
  intro D L hT Gi Gl Kc Dx cX ex t u w hg μ J hQ
  have hfr := GlobalTheory.Ggeo.FracLocal.isFractionRing_gat Gl u w hg
  have hrat := GlobalTheory.TwUChiRat.chiRatAll_of_adTie t u μ J.St J.A J.Hh.dt J.a J.tie J.kin
  have hpT : ∀ i (hi : i ≤ D.R.m), ¬ D.what₂.places.resChar w ∣ (J.St i hi).T := fun i hi => by
    rw [J.tie.T_eq i hi]; exact hg.2.2.2.2.2
  have hψ : ∀ i hi, PsiEx (foOf J.Hh J.St J.val i hi) (ex.cmp.embW u w hg) := fun i hi =>
    psiEx_of (foOf J.Hh J.St J.val i hi) (ex.cmp.embW u w hg) hfr (fun β => hrat (i + 1) hi β)
      (fun β => J.ord (i + 1) hi β)
  let Z : SiteD J.Gd.herm u w hg (ex.tw.fm u μ) :=
    { Fo := foOf J.Hh J.St J.val
      chFin := fun i hi => J.fin (i + 1) hi
      S := fun i hi =>
        { B := (Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E).symm (J.A.crd (i + 1) hi)⁻¹
          B_lat := fun β => GlobalTheory.T.inv_coords_isBasisAt_baseLattice_of_std_companion J.Gd.herm u w hg hi ((J.St (i + 1) hi).K β).lev (J.A.crd (i + 1) hi) J.a
            (hpT (i + 1) hi) (J.base (i + 1) hi β)
          ψ := fun β => (hψ i hi β).choose
          fin := fun β => fin_of _ β _ } }
  refine ⟨Z, rfl, ⟨fun i hi => hpT (i + 1) hi, fun i hi w' hw' => ?_, fun i hi => trivial⟩, ⟨fun i hi => ?_, fun i hi β => ?_, fun i hi β cl => ?_⟩,
    fun i hi => ?_⟩
  · exact GlobalTheory.TwU.not_mem_underSB_of_gIdx t u w hg μ hQ w' (J.tie.bad (i + 1) hi w' hw')
  · show cT (sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E
        ((Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E).symm (J.A.crd (i + 1) hi)⁻¹)).1 * gramN D (i + 1) hi *
      (Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E
        ((Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E).symm (J.A.crd (i + 1) hi)⁻¹)).1 = 1
    rw [MulEquiv.apply_symm_apply]
    exact std_of_C _ _ _ (J.pins.crd_orth (i + 1) hi)
  · exact (hψ i hi β).choose_spec
  · exact chRat_ofChiD J.chiD _ _ _
  · show Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E
        ((Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E).symm (J.A.crd (i + 1) hi)⁻¹) = _
    exact MulEquiv.apply_symm_apply _ _

end GlobalTheory.SiteEx
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsComparisonSiteDataOverChainChartsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_comparisonSiteData_over_chainCharts : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (μ : D.what₂.Tup) (J : JIn t u μ), (D.what₂.places.resChar w) ∉ Dx.Qp μ → ∃ Z : SiteD J.Gd.herm u w hg (ex.tw.fm u μ), Z.Fo = foOf J.Hh J.St J.val ∧ SiteGood Z ∧ SiteRest Z ex.cmp ∧ ∀ i hi, Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E (Z.S i hi).B = (J.A.crd (i + 1) hi)⁻¹ := by
  first | exact @GlobalTheory.SiteEx.siteD_exists | exact GlobalTheory.SiteEx.siteD_exists | (intros; apply GlobalTheory.SiteEx.siteD_exists <;> assumption)
end
end
