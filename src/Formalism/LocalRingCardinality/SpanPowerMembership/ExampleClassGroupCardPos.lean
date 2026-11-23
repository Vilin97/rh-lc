module

public import Formalism.LocalRingCardinality.SpanPowerMembership.Places
public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
public import Formalism.LocalRingCardinality.SpanPowerMembership.RelDet
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleWeightMiddleEntries
public import Formalism.LocalRingCardinality.SpanPowerMembership.FmZeroHLatEmpty
public import Formalism.SharpRestriction.CuspSpanNormBounds.DataS
public import Formalism.SharpRestriction.GrowthBounds.DataG
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleNewtypesIdempotentZero
public import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtB
public import Formalism.LocalRingCardinality.SpanPowerMembership.HaarDensityNeZero
public import Formalism.LocalRingCardinality.SpanPowerMembership.Adelic

-- Source module: Formalism.LocalRingCardinality.SpanPowerMembership.GPlacesExampleNatAct

section

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open Formalism.BasicNotions NumberField IsDedekindDomain

section S

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (sig : E →ₐ[F] E)

def locAdj (G : Finset ℕ) (loc : ∀ p, Formalism.MainNotions.S.Loc.LocAt F E sig p)
    (spl : ∀ p, Formalism.MainNotions.S.Loc.resChar p ∈ G →
      Formalism.MainNotions.S.Loc.SplitAt (loc p).Fp (loc p).Ep (loc p).cj (Formalism.MainNotions.S.Loc.resChar p))
    (p : HeightOneSpectrum (𝓞 F)) : Formalism.MainNotions.S.Loc.LocAt F E sig p :=
  { loc p with split := if h : Formalism.MainNotions.S.Loc.resChar p ∈ G then some (spl p h) else none }

theorem locAdj_split (G : Finset ℕ) (loc : ∀ p, Formalism.MainNotions.S.Loc.LocAt F E sig p)
    (spl : ∀ p, Formalism.MainNotions.S.Loc.resChar p ∈ G →
      Formalism.MainNotions.S.Loc.SplitAt (loc p).Fp (loc p).Ep (loc p).cj (Formalism.MainNotions.S.Loc.resChar p))
    (p : HeightOneSpectrum (𝓞 F)) :
    (locAdj sig G loc spl p).split.isSome ↔ Formalism.MainNotions.S.Loc.resChar p ∈ G := by
  unfold locAdj
  by_cases h : Formalism.MainNotions.S.Loc.resChar p ∈ G <;> simp [h]

variable {Word Tau : Type} [Subsingleton Word] (hc : Word → Tau → HCParam R)

def toySData (Del : ℚ) (hDel : 0 < Del)
    (hgap : ∀ (w : Word) (τ : Tau) (l : ℕ) (h : l + 1 < R.k - 1),
      (hc w τ).v ⟨l, by omega⟩ - (hc w τ).v ⟨l + 1, h⟩ = 4 * Del)
    (hlet : ∀ (w : Word) (τ : Tau) (l : ℕ) (h : l < R.k - 2),
      (hc w τ).u ⟨l + 1, by omega⟩ = (hc w τ).v ⟨l, by omega⟩ - 1 / 2)
    (loc : ∀ p, Formalism.MainNotions.S.Loc.LocAt F E sig p) :
    Formalism.MainNotions.S.Draft.SData R F E sig Word Tau hc where
  cdScale := fun _ _ => 1
  cdScale_pos := fun _ _ => one_pos
  Del := Del
  Del_pos := hDel
  cloud_gap := hgap
  letter := fun _ _ => false
  letter_inj := fun _ _ _ => Subsingleton.elim _ _
  u_letter := by
    intro w τ l h
    simp [hlet w τ l h]
  HH := EuclideanSpace ℂ (Fin 0)
  Cu := fun _ => EuclideanSpace ℂ (Fin 0)
  Pu := fun _ => 0
  volN := fun _ => 1
  volH := fun _ => 1
  volN_pos := fun _ => one_pos
  volH_pos := fun _ => one_pos
  Term := fun _ _ => Empty
  aTerm := fun _ _ t => t.elim
  isId := fun _ => False
  inS := fun _ => False
  relevant := fun _ => False
  FeqF := fun _ => False
  Gterm := fun t => t.elim
  atP := loc
  PlF := HeightOneSpectrum (𝓞 F)
  BBne := fun _ _ => False
  generic := fun _ => False
  Pair := fun _ _ => Empty
  pfst := fun t => t.elim
  psnd := fun t => t.elim
  s0 := fun _ => 0
  scalarPair := fun _ => False
  pval := fun _ => 0
  ptOf := fun t => t.elim
  cTerm := fun _ => 0
  massPair := fun _ => 0
  meanCount := fun _ _ _ => 0

variable {sig hc}

theorem toySData_HH (Del : ℚ) (hDel hgap hlet) (loc : ∀ p, Formalism.MainNotions.S.Loc.LocAt F E sig p) :
    Module.finrank ℂ (toySData sig hc Del hDel hgap hlet loc).HH = 0 := by
  show Module.finrank ℂ (EuclideanSpace ℂ (Fin 0)) = 0
  simp

def toySData_Cu (Del : ℚ) (hDel hgap hlet) (loc : ∀ p, Formalism.MainNotions.S.Loc.LocAt F E sig p) (u : Word)
    {V : Type} [AddCommGroup V] [Module ℂ V] (M : Submodule ℂ V) (hM : M = ⊥) :
    (toySData sig hc Del hDel hgap hlet loc).Cu u ≃ₗ[ℂ] M := by
  subst hM
  haveI : Subsingleton (EuclideanSpace ℂ (Fin 0)) := ⟨fun a b => by ext i; exact i.elim0⟩
  exact LinearEquiv.ofSubsingleton (EuclideanSpace ℂ (Fin 0)) (⊥ : Submodule ℂ V)

def toySData_PlF (Del : ℚ) (hDel hgap hlet) (loc : ∀ p, Formalism.MainNotions.S.Loc.LocAt F E sig p) :
    (toySData sig hc Del hDel hgap hlet loc).PlF ≃ HeightOneSpectrum (𝓞 F) := Equiv.refl _

end S

section G

open Formalism.MainNotions.G

def emptyPlaces (p : ℕ) : Places p ℤ_[3] ℚ_[3] where
  w := 0
  nV := 0
  n' := fun v => v.elim0
  W := fun v => v.elim0
  Qq := fun v => v.elim0
  ringW := fun v => v.elim0
  domW := fun v => v.elim0
  dvrW := fun v => v.elim0
  fieldQ := fun v => v.elim0
  algWQ := fun v => v.elim0
  ι := fun v => v.elim0
  σ := fun v => v.elim0
  j := fun v => v.elim0
  setting := fun v => v.elim0
  m := 0
  r := 0
  lam0 := fun v => v.elim0
  dom := fun v => v.elim0

instance (p : ℕ) : Unique (emptyPlaces p).Tup :=
  inferInstanceAs (Unique (∀ _ : Fin 0, _))

def toySignLevel (p : ℕ) : Level (emptyPlaces p) where
  Γ := ℤˣ
  act := fun v => v.elim0
  χ := Units.map (Int.castRingHom ℤ_[3]).toMonoidHom

theorem emptyPlaces_natAct (p : ℕ) (A : ∀ v, GL (Fin ((emptyPlaces p).m + 1)) ((emptyPlaces p).Qq v)) :
    (emptyPlaces p).natAct A = LinearMap.id := by
  have hs : ∀ G, (emptyPlaces p).subst G = AlgHom.id _ _ := by
    intro G
    apply MvPolynomial.algHom_ext
    rintro ⟨v, _⟩
    exact v.elim0
  unfold Places.natAct
  rw [hs, Finset.prod_eq_one (fun v _ => v.elim0), one_smul]
  rfl

def gAtPExample (p : ℕ) : GAtP p where
  O := ℤ_[3]
  Kf := ℚ_[3]
  P := emptyPlaces p
  comp := Unit
  lev := fun _ => toySignLevel p
  e := 0

theorem toySignLevel_M (p : ℕ) : (toySignLevel p).M = ⊥ := by
  rw [eq_bot_iff]
  intro F hF
  rw [Submodule.mem_bot]
  funext L
  have h := hF
  simp only [Level.M, Level.funMod, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at h
  have h1 := h.2 (show (toySignLevel p).Γ from (-1 : ℤˣ)) L
  have hs : (toySignLevel p).smul (show (toySignLevel p).Γ from (-1 : ℤˣ)) L = L := Subsingleton.elim _ _
  simp only [LinearMap.sub_apply, LinearMap.proj_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    hs] at h1
  have hc : ((toySignLevel p).χ (show (toySignLevel p).Γ from (-1 : ℤˣ)) : ℤ_[3]) = -1 := by
    show ((Units.map (Int.castRingHom ℤ_[3]).toMonoidHom (-1 : ℤˣ) : ℤ_[3]ˣ) : ℤ_[3]) = -1
    simp
  rw [hc] at h1
  have e : (((toySignLevel p).actX (show (toySignLevel p).Γ from (-1 : ℤˣ))).restrictScalars
      ℤ_[3]) (F L) = F L := by
    show (emptyPlaces p).natAct _ (F L) = F L
    rw [emptyPlaces_natAct]
    rfl
  rw [e, neg_one_smul, sub_neg_eq_add] at h1
  have h2 : (2 : ℚ_[3]) • F L = 0 := by rw [two_smul]; exact h1
  simpa using (smul_eq_zero.mp h2).resolve_left two_ne_zero

theorem gAtPExample_M (p : ℕ) : (gAtPExample p).M = ⊥ := by
  rw [eq_bot_iff]
  intro F hF
  rw [Submodule.mem_bot]
  funext i
  have h : F i ∈ (toySignLevel p).M := hF i (Set.mem_univ i)
  rw [toySignLevel_M] at h
  exact h

theorem gAtPExample_d (p : ℕ) : (gAtPExample p).d = 0 := by
  unfold GAtP.d
  rw [gAtPExample_M]
  exact finrank_bot _ _

end G

end Formalism.BasicNotions.Examples₂
end
end
end

-- Source module: Formalism.LocalRingCardinality.SpanPowerMembership.ExampleClassGroupCardPos

section

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain

structure LocalGap {R : Ranks} (H : Host R) where

  nloc : LocTheory

  nlocA : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (nloc l)

  nlocT : ∀ (l : ℕ) [Fact l.Prime], LocTied l (nloc l) (nlocA l)

theorem LocalGap.tame {R : Ranks} {H : Host R} (_G : LocalGap H) : TameHyp H := tameHyp H

def LocalGap.cd {R : Ranks} {H : Host R} (_G : LocalGap H) : CDHaar := CD.cdHaar

variable (H : Host R0) (T : ℕ) [hT : Fact T.Prime]

abbrev Tau0 : Type := ↥(R0.Psi)

theorem exampleClassGroupCard_pos {R : Ranks} (H : Host R) : 0 < exampleClassGroupCard H := by
  unfold exampleClassGroupCard
  refine Finset.prod_pos (fun k _ => pow_pos ?_ _)
  have : NeZero (H.g k) := ⟨(H.g_prime k).ne_zero⟩
  exact Nat.card_pos

abbrev rowsH : Rows.Data R0 :=
  toyRowsOfNumberField H.E H.φ₀ (@placesOf H.E _ _ H.cmStar) Tau0 card_examplePsi_eq (dstarOf T) (shaExample H)
    (shaExample_nonneg H) (exampleClassGroupCard H) (exampleClassGroupCard_pos H)

abbrev memT : Member R0 Tau0 (fun _ => hc0) := trivialMember Tau0 T (dstarOf T) (dstarOf_pos T)

theorem nHypH (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) :
    NHyp H (rowsH H T) :=
  { hsha := fun p _ e _ _ => shaExample_eq H p e
    hcard := rfl
    hg := hg }

theorem normAt_empty {K V ι : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] [IsEmpty ι] (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (x : V) :
    Formalism.HermitianLatticesTheory.normAt b X v x = 0 := by
  simp [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm]

def spH (pz : H.E) (hpz : pz * H.conj pz = (T : H.E)) :
    @Spaces R0 H.F H.E _ _ _ _ H.cmStar _ :=
  letI := H.cmStar
  spacesExample star_isIntegral (cmData H) T hT.out pz
    (by rw [star_eq_conj H pz, mul_comm]; exact hpz)
    (exists_adelic_neg_one H (cmData H).sig (fun x => star_eq_conj H x))

abbrev sDataH (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H) :
    Formalism.MainNotions.S.Draft.SData R0 H.F H.E (conjF H) Unit Tau0 (fun _ _ => hc0) :=
  toySData (conjF H) (fun _ _ => hc0) 1 one_pos (fun _ _ l h => exampleWeight_cloud_gap_four l h)
    (fun _ _ l h => exampleWeight_middle_entries l h) (locAdj (conjF H) {H.g 0, H.g 1} (slocH H)
      (fun p hp => (splH H hg ht.jac p hp).some))




def exampleRecordOfData
    (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H)
    (hlev : T ∈ H.levelPrimes) (hpde : T ≠ H.pde ∧ T ≠ H.pde')
    (pz : 𝓞 H.E) (hK : (pz : H.E) ∈ H.K) (hpz : (pz : H.E) * H.conj (pz : H.E) = (T : H.E))
    (hcong : (pz - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)})
    (G : LocalGap H) : D7 :=
  letI : StarRing H.E := H.cmStar
  { R := R0
    host := H
    sp := spH H T pz hpz
    what₂ := rowsH H T
    eTau := Equiv.refl _
    hc := fun _ => hc0
    wordFin := inferInstanceAs (Fintype Unit)
    u₀ := ()
    hcW := fun _ _ => hc0
    hcW_base := rfl
    hcW_v := fun _ _ => rfl
    hcW_b := fun _ _ => rfl
    hcW_e := fun _ _ => rfl
    hcW_first := fun _ _ _ => rfl
    hcW_last := fun _ _ _ => rfl
    mem := fun _ => memT T
    nfLL := inferInstanceAs (NumberField H.E)
    starLL := H.cmStar
    tcLL := instTotallyComplex H
    galLL := instIsGalois H
    starLL_cx := fun x => emb_star H H.φ₀ x
    div := toyZeroLatticeDatum H.E
    div_good := ⟨(zeroHLat_good H.E).1, fun _ => (zeroHLat_good H.E).1⟩
    embE := RingHom.id _
    embE_φ₀ := rfl
    conjF := conjF H
    conjF_eq := conjF_apply H
    embE_conj := fun x => (star_eq_conj H x).symm
    LL0 := ⊤
    hostField_le_fixedField := fun _ => IntermediateField.mem_top
    O_contains := fun x => ⟨x, rfl⟩
    plEq := Equiv.refl _
    val_eq := placesOf_val_eq H.E
    ram_eq := placesOf_ram_eq H.E
    conj_val := placesOf_conj_val H.E
    T_level := fun _ => hlev
    T_norm := fun _ => ⟨pz, hK, hpz, hcong⟩
    sp_T := rfl
    cOf := fun _ => 1
    cOf_ne := fun _ => one_ne_zero
    cOf_eq := fun _ => by rw [map_one, one_mul, one_mul]
    T_win := fun _ => exampleLevel_near_lower Tau0 T
    GamP_eq := fun _ => rfl
    T_ne_pde := fun _ => hpde
    Dstar_eq := fun _ => rfl
    clsLat := fun _ _ c => Empty.elim c
    clsLat_lat := fun _ _ c => Empty.elim c
    eMu := fun _ => toyZeroSpaceEquiv Tau0 T (dstarOf T) (dstarOf_pos T)
    eMt := fun _ => toyZeroSpaceRefl
    perCol_base_eq_PtilCol := fun _ _ _ => rfl
    Bu_linL := fun _ _ => zero_isLinear
    Bu_linR := fun _ _ => zero_isLinear
    chTw := fun _ _ => (memT T).C
    memberColumns_twistedChain_base := fun _ => rfl
    e0Tw := fun _ _ => LinearEquiv.refl ℂ _
    PTw := fun _ _ => (memT T).P
    eMtTw := fun _ _ => toyZeroSpaceRefl
    perCol_tie := fun _ _ h => absurd rfl h
    vol := fun _ => 1
    vol_pos := fun _ => one_pos
    O_int := fun y => RingOfIntegers.isIntegral_coe y
    jEE := jZero H.E H.φ₀
    jEE_basis := jZero_basis H.E H.φ₀
    jN := fun _ => jZero H.E H.φ₀
    jN_basis := fun _ => jZero_basis H.E H.φ₀
    Dall_eq := rfl
    delP_eq := rfl
    Dt := ℂˣ
    detCls := fun _ _ _ => 1
    muTil := fun _ => 1
    chiD := MonoidHom.id _
    UO := ⊥
    chiD_UO := fun _ hx => Subgroup.mem_bot.mp hx
    e1Dt := exampleInverseEmbeddingProduct H (Equiv.refl Tau0)
    rest_detCharacter_on_unitary_eq := exampleCharacter_unitary_product H (Equiv.refl Tau0)
    relDet := fun N L L' => QuotientGroup.mk (relDetExample H (Equiv.refl Tau0) N L L')
    relDet_self := fun N L => by rw [relDetExample_self]; rfl
    relDet_mul := fun N L L' L'' => by rw [← QuotientGroup.mk_mul, relDetExample_mul]
    relDet_smul := fun N L L' γ h => congrArg _ (relDetExample_smul H (Equiv.refl Tau0) N L L' γ h)
    rhoDet_eq_inv_muTilde_chiD_pow := fun _ _ c => Empty.elim c
    rhoDetPrime_eq_muTilde_mul_chi_pow := fun _ i c => Empty.elim c
    dsig := toyConstantOne _
    dsig_pos := toyConstantOne_pos _
    s := sDataH H hg ht
    s_split := locAdj_split (conjF H) {H.g 0, H.g 1} (slocH H)
      (fun p hp => (splH H hg ht.jac p hp).some)
    s_HH := toySData_HH _ _ _ _ _
    s_Cu := fun u => toySData_Cu _ _ _ _ _ u _ rfl
    s_PlF := toySData_PlF _ _ _ _ _
    loc := G.nloc
    locA := G.nlocA
    locT := G.nlocT
    nd := ndToy H (rowsH H T) (nHypH H T hg)
    ntw := ntwToy H ⊤ (nHypH H T hg)
    naut := nautToy H (rowsH H T) (nHypH H T hg)
    nbc := nbcToy H (rowsH H T) (nHypH H T hg)
    nexp := nexpToy H ⊤ (nHypH H T hg)
    ntypes := ntypesT H (rowsH H T) (nHypH H T hg) ht G.tame
    nStage_trivialCharacter_compat := @ntypesT_E0Tie _ H (rowsH H T) (nHypH H T hg)
      (fun _ => inferInstanceAs (Subsingleton Z0)) (fun _ _ => inferInstanceAs (Subsingleton Z0)) ht G.tame
    nth := nthToy H ⊤ (nHypH H T hg)
    nbr := fun i => Empty.elim i
    self_good := fun i => Empty.elim i
    ntwbr := fun i => Empty.elim i
    nbr_ind := fun i => Empty.elim i
    ntwbr_ind := fun i => Empty.elim i
    loc_tie := fun i => Empty.elim i
    bc_tie := fun i => Empty.elim i
    rbar_tie := fun i => Empty.elim i
    mtpar_tie := fun i => Empty.elim i
    jetW := fun i => Empty.elim i
    jetW_l := fun i => Empty.elim i
    jetTau := fun i => Empty.elim i
    jetW1 := fun i => Empty.elim i
    resChar_thetaJetPlaceDegOne := fun i => Empty.elim i
    jetTau1 := fun i => Empty.elim i
    nStage_trivialCharacter_coeff_eq := fun g => (map_zero H.φ₀).trans (newtypes_idempotent_zero H _ _ ht G.tame g).symm
    Z_tie := example_Z_compatibility H _ _
    Zgood_tie := example_goodZ_compatibility H _ _
    etaJ_tie := example_etaJ_compatibility H _ _ (fun _ _ => rfl)
    fm := fun _ => formsToy H.φ₀ (placesOf H.E) card_examplePsi_eq (memT T).C (memT T).A (memT T).P
    eMu_isom := fun _ φ ψ => by
      rw [Subsingleton.elim φ 0, inner_zero_left]
      exact (Finset.sum_of_isEmpty _).symm
    nuIn := fun _ => 0
    nuIn_inj := fun _ x y _ => Subsingleton.elim (α := Fin 0 → H.E) x y
    nuIn_range := fun _ => Subsingleton.elim (α := Submodule H.E (Fin 0 → H.E)) _ _
    nuIn_jN := fun _ _ => funext fun c => Empty.elim c
    nuIn_norm := fun _ v x => by
      exact (normAt_empty (ι := Fin 0) _ _ _ _).trans (normAt_empty (ι := Fin 0) _ _ _ _).symm
    jEE_norm := fun x => by
      exact (normAt_empty (ι := Fin 0) _ _ _ _).trans (norm_zero (E := Z0)).symm
    sEE := ⟨0, fun x => (norm_zero (E := Z0)).trans
      ((norm_zero (E := Z0)).symm.trans (congrArg norm (Subsingleton.elim (α := Z0) 0 x)))⟩
    s_Cu_isom := fun _ φ ψ => by
      rw [Subsingleton.elim (α := Z0) φ 0]
      exact (inner_zero_left (𝕜 := ℂ) (E := Z0) ψ).trans (Finset.sum_of_isEmpty _).symm
    cd := G.cd
    jet := jetToy R0 H
    jetU := fun i => Empty.elim i
    jetL := fun i => Empty.elim i
    jetL' := fun i => Empty.elim i
    jetU1 := fun i => Empty.elim i
    jetL1 := fun i => Empty.elim i
    jetL1' := fun i => Empty.elim i
    gx := gxExample _ _
    gat := fun _ _ _ => gAtPExample _
    gat_d := fun _ _ _ => (gAtPExample_d _).trans (finrank_bot ℂ _).symm
    Y_sigval := spacesExample_Ysig _ _ _ _ _ _ _ }

end Formalism.BasicNotions.Examples₂
end
end
end
