package org.kframework.parser

import org.apache.commons.lang3.StringEscapeUtils

import org.kframework.minikore.interfaces.pattern._
import org.kframework.minikore.interfaces.build.Builders

import org.kframework.minikore.converters.KoreToMini._
import org.kframework.minikore.implementation.MiniKore.{Definition, Module, Sentence, Import, SortDeclaration, SymbolDeclaration, Attributes, Rule, Axiom}


case class EKOREDefinition(b: Builders) {

  val meta = org.kframework.minikore.MiniKoreMeta(b)
  val patternUtils = org.kframework.minikore.MiniKorePatternUtils(b)
  val outerUtils = org.kframework.minikore.MiniKoreOuterUtils(b)
  val karserDsl = KarserDSL(b)
  val koreDef = KOREDefinition(b)

  import org.kframework.minikore.converters.KoreToMini.{iMainModule, iEntryModules}
  import org.kframework.minikore.implementation.MiniKore.Module
  import org.kframework.minikore.implementation.MiniKoreDSL._
  import b._
  import meta._
  import patternUtils._
  import outerUtils._
  import karserDsl._
  import koreDef._

  // Utilities
  // =========

  def stripString(front: Int, back: Int): String => String = (str: String) => StringEscapeUtils.unescapeJava(str drop front dropRight back)

  def removeSubNodes(label: Symbol): Pattern => Pattern = {
    case Application(name, args) => Application(name, args filterNot { case Application(`label`, _) => true case _ => false })
    case pattern                 => pattern
  }

  // Normalization passes
  // ====================

  val removeParseInfo: Pattern => Pattern = {
    case Application(Symbol("#"), Application(Symbol("#"), actual :: _) :: _) => actual
    case pattern                                                              => pattern
  }

  val KStringKTOKENS   = Symbol("#String@KTOKENS")
  val KPatternKPATTERN = Symbol("#Pattern@KPATTERN")

  val normalizeTokens: Pattern => Pattern = {
    // case dv@DomainValue("KSymbol@KTOKENS", _)     => upDomainValue(dv)
    case DomainValue(`KStringKTOKENS`, str)    => upDomainValue(DomainValue(KStringKTOKENS, stripString(1, 1)(str)))
    case DomainValue(`KPatternKPATTERN`, name) => upPattern(Application(Symbol(name), Seq.empty))
    case pattern                               => pattern
  }

  // Disagreements on encoding
  // =========================

  val toKoreEncodingProdItems: Pattern => Pattern = {
    case Application(`KTerminal`, DomainValue(`KValue`, term) :: DomainValue(`KValue`, follow) :: Nil)                                         => Application(iTerminal, Seq(S(term), S(follow)))
    case Application(`KTerminal`, DomainValue(`KValue`, term) :: Nil)                                                                          => Application(iTerminal, Seq(S(term)))
    case Application(`KRegexTerminal`, DomainValue(`KValue`, precede) :: DomainValue(`KValue`, regex) :: DomainValue(`KValue`, follow) :: Nil) => Application(iRegexTerminal, Seq(S(precede), S(regex), S(follow)))
    case Application(`KNonTerminal`, DomainValue(`KValue`, sort) :: Nil)                                                                       => Application(iNonTerminal, Seq(S(sort)))
  }

  val toKoreEncodingAttributes: Pattern => Pattern = {
    case Application(`iMainModule`, Seq(Application(Symbol(modName), Nil)))   => Application(iMainModule, Seq(S(modName)))
    case Application(`iEntryModules`, Seq(Application(Symbol(modName), Nil))) => Application(iEntryModules, Seq(S(modName)))
    case Application(`KPriorityDeclaration`, Seq(ksp))                             => Application(iSyntaxPriority, flattenBySymbols(KPriorityItems, KPriorityItemsMt)(ksp))
    case Application(`KProduction`, args)                                     => Application(Symbol("production"), args map toKoreEncodingProdItems)
    case pattern                                                              => pattern
  }

  val toKoreEncodingSentences: Sentence => Sentence = {
    case Import(name, atts)                         => Import(name, atts map toKoreEncodingAttributes)
    case SortDeclaration(sort, atts)                => SortDeclaration(sort, atts map toKoreEncodingAttributes)
    case SymbolDeclaration(sort, label, args, atts) => SymbolDeclaration(sort, label, args, atts map toKoreEncodingAttributes)
    case Rule(pattern, atts)                        => Rule(pattern, atts map toKoreEncodingAttributes)
    case Axiom(pattern, atts)                       => Axiom(pattern, atts map toKoreEncodingAttributes)
  }

  val toKoreEncodingMod: Module => Module = {
    case Module(name, sentences, atts) =>
      val koreEncodingAttributes = atts map toKoreEncodingAttributes
      val priorityDummyAxioms = getAttributeKey(iSyntaxPriority, koreEncodingAttributes) map (kp => dummySentence(Seq(Application(iSyntaxPriority, kp map (kpg => Application(iSyntaxPriorityGroup, flattenBySymbols(KSymbolList, KSymbolListMt)(kpg)))))))
      Module(name, (sentences ++ priorityDummyAxioms) map toKoreEncodingSentences, koreEncodingAttributes)
  }

  val toKoreEncodingDef: Definition => Definition = {
    case Definition(modules, atts) => Definition(modules map toKoreEncodingMod, atts map toKoreEncodingAttributes)
  }

  // Preprocessing
  // =============

  val preProcess: Pattern => Pattern = traverseTopDown(removeParseInfo) andThen traverseBottomUp(normalizeTokens)


  // EKORE Definition
  // ================

  // K-PRETTY-PRODUCTION
  // ===================

  val STerminal                 = Sort("Terminal")
  val SRegexTerminal            = Sort("RegexTerminal")
  val SNonTerminal              = Sort("NonTerminal")
  val SProduction               = Sort("Production")
  val SProductions              = Sort("Productions")
  val SProductionsBlock         = Sort("ProductionsBlock")
  val SPriority                 = Sort("Priority")
  val SProductionWithAttributes = Sort("ProductionWithAttributes")

  val KProductionWithAttributes = Symbol("#ProductionWithAttributes")
  val KProductionsBlock         = Symbol("#ProductionsBlock")
  val KProductionsPriority      = Symbol("#ProductionsPriority")
  val KPriorityItemsMt          = Symbol("#.PriorityItems")
  val KPriorityItems            = Symbol("#PriorityItems")
  val KSyntaxDeclaration        = Symbol("#SyntaxDeclaration")
  val KPriorityDeclaration      = Symbol("#PriorityDeclaration")

  val K_PRETTY_PRODUCTION: Module = module("K-PRETTY-PRODUCTION",
    imports("KDEFINITION"),

    syntax(STerminal)      is Regex(KRegexString)       att("token"),
    syntax(SRegexTerminal) is Regex("r" + KRegexString) att("token"),
    syntax(SNonTerminal)   is Regex(KRegexSymbol)       att("token"),

    syntax(SProduction) is STerminal                  att(),
    syntax(SProduction) is SRegexTerminal             att(),
    syntax(SProduction) is SNonTerminal               att(),
    syntax(SProduction) is (SProduction, SProduction) att(kLabel(KProduction), "assoc"),

    syntax(SProductionWithAttributes) is (SProduction, SAttributes) att(kLabel(KProductionWithAttributes)),

    syntax(SProductionsBlock) is SProductionWithAttributes                           att(),
    syntax(SProductionsBlock) is (SProductionWithAttributes, "|", SProductionsBlock) att(kLabel(KProductionsBlock)),

    syntax(SProductions) is SProductionsBlock                      att(),
    syntax(SProductions) is (SProductionsBlock, ">", SProductions) att(kLabel(KProductionsPriority), "assoc"),

    syntax(SPriority) is ""                          att(kLabel(KPriorityItemsMt)),
    syntax(SPriority) is SSymbolList                 att(),
    syntax(SPriority) is (SPriority, ">", SPriority) att(kLabel(KPriorityItems), "assoc"),

    syntax(SSentence) is ("syntax", SSymbol, SAttributes)         att(kLabel(KSortDeclaration)),
    syntax(SSentence) is ("syntax", SSymbol, "::=", SProductions) att(kLabel(KSyntaxDeclaration)),
    syntax(SSentence) is ("syntax", "priority", SPriority)        att(kLabel(KPriorityDeclaration))
  )

  // TODO: correctly process precede/follow regex clauses
  val normalizeProductionItems: Pattern => Pattern = {
    // case DomainValue(name@"KTerminal@K-PRETTY-PRODUCTION", term)       => )application(name, stripString(1, 1)(term))
    // case DomainValue(name@"KRegexTerminal@K-PRETTY-PRODUCTION", rterm) => Application(name, Seq(Application("#", Nil), Application(stripString(2, 1)(rterm), Nil), Application("#", Nil)))
    // case DomainValue(name@"KNonTerminal@K-PRETTY-PRODUCTION", nterm)   => application(name, nterm)
    case pattern                                                       => pattern
  }

  val desugarPrettySentence: Pattern => Seq[Pattern] = {

    case Application(`KSyntaxDeclaration`, sort :: Application(`KProductionWithAttributes`, production :: atts :: Nil) :: Nil) =>
      val pis = flattenBySymbols(KProduction)(production) map downProductionItem
      val symbDecl: SymbolDeclaration = syntax(downSort(sort), pis) att(downAttributes(atts):_*)
      Seq(upSentence(symbDecl))

    case Application(`KSyntaxDeclaration`, sort :: (kpb@Application(`KProductionsBlock`, _)) :: Nil) =>
      val sents        = flattenBySymbols(KProductionsBlock)(kpb) flatMap (kp => desugarPrettySentence(Application(KSyntaxDeclaration, Seq(sort, kp))))
      val klabels      = sents collect { case Application(`KSymbolDeclaration`, _ :: klabel :: _ :: _ :: Nil) => klabel }
      val prioritySent = Application(KPriorityDeclaration, Seq(consListLeftSubsort(KSymbolList, KSymbolListMt)(klabels)))
      sents :+ prioritySent

    case Application(`KSyntaxDeclaration`, sort :: (kpp@Application(`KProductionsPriority`, _)) :: Nil) =>
      val kpbs                 = flattenBySymbols(KProductionsPriority)(kpp) flatMap (kpb => desugarPrettySentence(Application(KSyntaxDeclaration, Seq(sort, Application(KProductionsBlock, Seq(kpb))))))
      val (pBlocks, prodSents) = kpbs partition { case Application(`KPriorityDeclaration`, _) => true case _ => false }
      val prioritySent         = Application(KPriorityDeclaration, Seq(consListLeftSubsort(KPriorityItems, KPriorityItemsMt)(pBlocks map { case Application(`KPriorityDeclaration`, pBlock :: Nil) => pBlock })))
      prodSents :+ prioritySent

    case pattern => Seq(pattern)
  }

  val desugarPrettyModule: Pattern => Pattern = {

    case Application(`KModule`, name :: sentences :: atts :: Nil) =>
      val desugaredSentences         = flattenBySymbols(KSentenceList, KSentenceListMt)(sentences) flatMap desugarPrettySentence
      val (priorities, newSentences) = desugaredSentences partition { case Application(`KPriorityDeclaration`, _) => true case _ => false }
      val newModule = module(downName(name), (newSentences map downSentence):_*) att((downAttributes(atts) ++ priorities):_*)
      upModule(newModule)

    case pattern => pattern
  }

  // K-CONCRETE-RULES
  // ================

  val KBubbleRegex = "[^ \n\r\t]+"

  val KBubbleItem = Symbol("#BubbleItem")
  val KBubble     = Symbol("#Bubble")

  val SBubbleItem = Sort("BubbleItem")
  val SBubble     = Sort("Bubble")

  val K_CONCRETE_RULES: Module = module("K-CONCRETE-RULES",
    imports("KPATTERN"),

    syntax(SBubbleItem) is Regex(KBubbleRegex) att("avoid", "token", term("reject2", term("rule|syntax|endmodule|configuration|context"))),

    syntax(SBubble) is (SBubble, SBubbleItem) att(kLabel(KBubble), "avoid"),
    syntax(SBubble) is SBubbleItem            att("avoid"),

    syntax(SPattern) is SBubble att()
  )

  def mkRuleParserDefinition(astDef: Pattern): Definition = {
    val defn = downDefinition(traverseTopDown(removeSubNodes(KRule))(astDef))
    val mainModuleName = getAttributeKey(iMainModule, defn.att) match { case Seq(Seq(Application(Symbol(name), Nil))) => name }
    val sorts = allSorts(defn) toSeq
    val newSentences = sorts flatMap (sort => Seq(syntax(sort) is SVariable, syntax(SPattern) is sort)) map (_.att())
    val ruleParserModuleName = mainModuleName + "-RULE-PARSER"
    val ruleParserModule = Module(ruleParserModuleName, imports(mainModuleName).att() +: imports("KPATTERN").att() +: newSentences, Seq.empty)
    val ruleParserAtts = updateAttribute(iMainModule, Application(ruleParserModuleName, Nil)) andThen updateAttribute(iEntryModules, Application(ruleParserModuleName, Nil))
    Definition(defn.modules :+ ruleParserModule :+ KPATTERN :+ KTOKENS, ruleParserAtts(defn.att))
  }

  def mkParser(d: Definition): String => Pattern = input => {
    import org.kframework.parser.concrete2kore.ParseInModule
    import org.kframework.attributes.Source
    import org.kframework.kore.ADT.SortLookup
    import org.kframework.minikore.converters.MiniToKore
    import org.kframework.minikore.converters.KoreToMini

    val parser = new ParseInModule(MiniToKore(toKoreEncodingDef(d)).mainModule)
    parser.parseString(input, SortLookup("#Pattern"), Source(""))._1 match {
      case Right(x) => KoreToMini(x)
      case Left(y) => throw new Error("runParser error: " + y.toString)
    }
  }

  def resolveBubbles(parser: String => Pattern): Pattern => Pattern = {
    case b@Application(`KBubble`, _) => preProcess(parser(flattenBySymbols(KBubble)(b) map { case DomainValue(KBubbleItem, str) => str } mkString " "))
    case pattern                     => pattern
  }

  val upUserPattern: Pattern => Pattern = {
    case sym@Application(`KDomainValue`, _)                                             => sym
    case Application(label, args) if (KTOKENS_LABELS ++ KPATTERN_LABELS) contains label => Application(label, args map upUserPattern)
    case Application(label, args)                                                       => Application(`KApplication`, Seq(upSymbol(label), consListLeft(`KPatternList`, `KPatternListMt`)(args map upUserPattern)))
  }

  def resolveRule(parser: String => Pattern): Pattern => Pattern = {
    case Application(`KRule`, rule :: atts :: Nil) => Application(KRule, Seq(upUserPattern(traverseTopDown(resolveBubbles(parser))(rule)), atts))
    case pattern                                   => pattern
  }

  def resolveDefinitionRules(parsed: Pattern): Pattern = traverseTopDown(resolveRule(mkParser(mkRuleParserDefinition(parsed))))(parsed)

  // EKORE
  // =====

  val EKORE_MODULE: Module = module("EKORE",
    imports("K-PRETTY-PRODUCTION"),
    imports("K-CONCRETE-RULES")
  )

  val EKORE = definition((KORE.modules :+ K_PRETTY_PRODUCTION :+ K_CONCRETE_RULES :+ EKORE_MODULE):_*) att(term(iMainModule, term("EKORE")), term(iEntryModules, term("EKORE")))

  val ekoreToKore: Pattern => Pattern = traverseTopDown(desugarPrettyModule)
}
