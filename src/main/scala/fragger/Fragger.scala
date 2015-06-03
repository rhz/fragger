package fragger

import scala.collection.mutable
import scala.scalajs.js
import js.annotation.JSExport
import org.scalajs.dom.{document,html,localStorage}
import scalatags.JsDom.all._
import scala.util.parsing.combinator._
import graph_rewriting._
import implicits._
import moments._


object Fragger extends js.JSApp {

  type N = String
  type E = IdDiEdge[Int,N]
  type L = String
  val Graph = MarkedDiGraph.withType[N,L,E,L]
  type Graph = MarkedDiGraph[N,L,E,L]

  object GraphParser extends Parsers with RegexParsers {

    lazy val ident: Parser[String] = """\w+""".r | failure("an identifier was expected")

    lazy val graph: Parser[Graph] =
      // rep((node <~ ";") | (edge <~ ";")) ^^ {
      repsep(edge | markedNode | inMarkedNode | outMarkedNode | node |
        failure("a node or an edge was expected"), ";" | ",") <~ opt(";" |
          failure("'->' or ',' or ';' was expected")) ^^ {
        nodesAndEdges =>
        val g = Graph()()
        var i = 0
        for (nodeOrEdge <- nodesAndEdges) nodeOrEdge match {
          case Node(name,label,mark) => {
            g += name
            if (label.isDefined)
              g(name).label = label.get
            mark match {
              case 0 => ()
              case 1 => g(name).inMark
              case 2 => g(name).outMark
              case 3 => g(name).mark
            }
          }
          case Edge(source,target,label) => {
            val e = IdDiEdge(i,source,target)
            i += 1
            g += e
            if (label.isDefined)
              g(e).label = label.get
          }
        }
        g
      }

    lazy val node: Parser[Node] = ident ~ label ^^ {
      case name ~ label => Node(name,label,0) }

    lazy val inMarkedNode: Parser[Node] = (">" ~> ident <~ "<") ~ label ^^ {
      case name ~ label => Node(name,label,1) }

    lazy val outMarkedNode: Parser[Node] = ("<" ~> ident <~ ">") ~ label ^^ {
      case name ~ label => Node(name,label,2) }

    lazy val markedNode: Parser[Node] = ("|" ~> ident <~ "|") ~ label ^^ {
      case name ~ label => Node(name,label,3) }

    lazy val edge: Parser[Edge] = ident ~ arrow ~ ident ^^ {
      case source ~ label ~ target => Edge(source,target,label) }

    lazy val arrow: Parser[Option[L]] =
      ("->" ~> label) | failure("'->' or ';' was expected")

    lazy val label: Parser[Option[L]] = opt("[" ~> ident <~ "]")

    sealed abstract class NodeOrEdge
    case class Node(name: N, label: Option[L], mark: Int) extends NodeOrEdge
    case class Edge(source: N, target: N, label: Option[L]) extends NodeOrEdge

    def parse(s: String, errorDiv: html.Div, pos: String): Graph =
      parse(super[Parsers].phrase(graph),s) match {
        case Success(g,_) => g
        case NoSuccess(msg,next) => {
          errorDiv.appendChild(div(cls:="alert alert-danger")(
            s"Error parsing $pos: " + msg.replace("`","'") + " " +
              (if (next.pos.column <= 1) "at the beginning of expression"
               else  s"after '${s.substring(0,next.pos.column-1)}'.")).render)
          throw new IllegalArgumentException(
            s"string '$s' couldn't be parsed as a graph")
        }
      }
  }

  class ObsNaming(obs: Seq[(String,Graph)], start: Int = 0)
      extends GraphNaming[N,L,E,L,MarkedDiGraph] {

    val cnt = utils.Counter(start)
    val index = mutable.Map[Graph,Int]()
    val isos = mutable.Map[Graph,Graph]()

    def apply(g: Graph): String =
      obs.find(_._2 iso g) match {
        case Some((name,_)) => name
        case None =>
          if (index contains g) s"F${index(g)}"
          else if (isos contains g) s"F${index(isos(g))}"
          else index find { case (h,_) => g iso h } match {
            case Some((h,_)) => { isos(g) = h; s"F${index(h)}" }
            case None => { val i = cnt.next; index(g) = i; s"F$i" }
          }
      }

    def seq: Seq[(Graph,String)] = obs.map(_.swap) ++ (
      for ((g,i) <- index.toSeq.sortBy(_._2))
      yield (toIntNodes(g),s"F$i"))

    def toIntNodes(g: Graph): Graph = {
      val nodes = g.nodes.zipWithIndex.toMap
      val edges = for (e <- g.edges) yield IdDiEdge(e.id,
        nodes(e.source).toString,nodes(e.target).toString)
      val h = Graph(nodes.values.map(_.toString),edges)
      for (n <- g.inMarks) h(n).inMark
      for (n <- g.outMarks) h(n).outMark
      h
    }
  }

  case class RuleInput(name: html.Input, lhs: html.Input, rhs: html.Input)
  case class ObsInput(name: html.Input, graph: html.Input)

  val rules = mutable.ArrayBuffer.empty[RuleInput]
  val obs = mutable.ArrayBuffer.empty[ObsInput]

  def newRule: html.Div = {
    val name = input(tpe:="text",width:="100%").render
    val lhs = input(tpe:="text",width:="100%").render
    val rhs = input(tpe:="text",width:="100%").render
    rules += RuleInput(name,lhs,rhs)
    div(cls:="row",margin:=10)(
      div(cls:="col-md-1")(name),
      div(cls:="col-md-5")(lhs),
      div(cls:="glyphicon glyphicon-arrow-right col-md-1",
        aria.hidden:=true,style:="line-height:35px"),
      div(cls:="col-md-5")(rhs)).render
  }

  def newObs: html.Div = {
    val name = input(tpe:="text",width:="100%").render
    val graph = input(tpe:="text",width:="100%").render
    obs += ObsInput(name,graph)
    div(cls:="row",margin:=10)(
      div(cls:="col-md-2")(name),
      div(cls:="col-md-10")(graph)).render
  }

  val n: Int = 3 // initial number of rules and observables
  val ruleDiv: html.Div = div(for (i <- 1 to n) yield newRule).render
  val obsDiv: html.Div = div(for (i <- 1 to n) yield newObs).render
  val maxNumEqs: html.Input = input(tpe:="text",size:=3,value:="10").render
  val errorDiv: html.Div = div().render
  val resultDiv: html.Div = div().render

  val addRule = () => ruleDiv.appendChild(newRule)
  val addObs = () => obsDiv.appendChild(newObs)
  val genEquations = () => {
    errorDiv.innerHTML = ""
    val rs = for {
      r <- rules
      if r.name.value != ""
    } yield Rule(
      GraphParser.parse(r.lhs.value,errorDiv,
        s"the left-hand side of rule '${r.name.value}'"),
      GraphParser.parse(r.rhs.value,errorDiv,
        s"the right-hand side of rule '${r.name.value}'"),
      Rate(r.name.value))
    println(rs)
    val os = for {
      o <- obs
      if o.name.value != ""
    } yield (o.name.value,
      GraphParser.parse(o.graph.value,errorDiv,
        s"observable '${o.name.value}'"))
    val odes = generateMeanODEs[N,L,E,L,MarkedDiGraph](
      maxNumEqs.value.toInt,rs,os.map(_._2))
    // FIXME: Better output
    val p = ODEPrinter(odes)
    val name = new ObsNaming(os)
    val lines = for (ODE(lhs,rhs) <- p.simplify) yield (
      s"d(${name(lhs)})/dt = " + (if (rhs.isEmpty) "0" else
        rhs.terms.map(p.strMn(_,name)).mkString(" + ")))
    def toDot(g: Graph) =
      (for (n <- g.nodes) yield
        if (g(n).inMarked && g(n).outMarked) "|" + n + "|"
        else if (g(n).inMarked) ">" + n + "<"
        else if (g(n).outMarked) "<" + n + ">"
        else n).mkString(", ") + (
        if (g.nodes.isEmpty || g.edges.isEmpty) "" else ", ") +
      (for (e <- g.edges) yield
        s"${e.source}->${e.target}").mkString(", ")
    val names = for ((g,n) <- name.seq)
                yield s"$n := ${toDot(g)}"
    // resultDiv.innerHTML = ""
    resultDiv.appendChild(
      div(cls:="row",margin:=10)(h2("Results")).render)
    resultDiv.appendChild(
      textarea(style:="margin-bottom:50px; width:100%; height:" +
      ((names.size + lines.size + 1) * 30) + "px")(
      names.mkString("\n") + "\n\n" + lines.mkString("\n")).render)
  }

  def serialiseModel: String = {
    val rs = (for {
      RuleInput(name,lhs,rhs) <- rules
      if name.value != ""
    } yield {
      if (name.value.contains('"') ||
           lhs.value.contains('"') ||
           rhs.value.contains('"')) {
        errorDiv.innerHTML = ""
        errorDiv.appendChild(div(cls:="alert alert-danger")(
          "Rules can't contain quotes (\").").render)
        throw new IllegalArgumentException(
          "Rules can't contain quotes (\").")
      } else s"""("${name.value}","${lhs.value}","${rhs.value}")"""
    }).mkString(";")
    val os = (for {
      ObsInput(name,graph) <- obs
      if name.value != ""
    } yield {
      if (name.value.contains('"') ||
         graph.value.contains('"')) {
        errorDiv.innerHTML = ""
        errorDiv.appendChild(div(cls:="alert alert-danger")(
          "Observables can't contain quotes (\").").render)
        throw new IllegalArgumentException(
          "Observables can't contain quotes (\").")
      } else s"""("${name.value}","${graph.value}")"""
    }).mkString(";")
    println(s"{rules:[$rs],obs:[$os]}")
    s"{rules:[$rs],obs:[$os]}"
  }

  val Model = """{rules:\[(.*)\],obs:\[(.*)\]}""".r
  val Triple = """\("(.*)","(.*)","(.*)"\)""".r
  val Twople = """\("(.*)","(.*)"\)""".r
  def deserialiseModel(s: String) = s match {
    case Model(rs,os) => {
      rules.clear
      obs.clear
      ruleDiv.innerHTML = ""
      obsDiv.innerHTML = ""
      for (Triple(name,lhs,rhs) <- rs.split(";")) {
        println(s"($name,$lhs,$rhs)")
        ruleDiv.appendChild(newRule)
        val RuleInput(n,l,r) = rules.last
        n.value = name
        l.value = lhs
        r.value = rhs
      }
      for (Twople(name,graph) <- os.split(";")) {
        println(s"($name,$graph)")
        obsDiv.appendChild(newObs)
        val ObsInput(n,g) = obs.last
        n.value = name
        g.value = graph
      }
    }
    case _ => {
      errorDiv.innerHTML = ""
      errorDiv.appendChild(div(cls:="alert alert-danger")(
        s"Model '$s' couldn't be deserialised.").render)
    }
  }

  val modelName: html.Input = input(tpe:="text",width:="100%").render
  val loadModel = () =>
    if (modelName.value == "") {
      errorDiv.innerHTML = ""
      errorDiv.appendChild(div(cls:="alert alert-danger")(
        "You didn't provide a name for the model.").render)
    } else if ((localStorage.getItem("models") != null) &&
      (localStorage.getItem("models").split(",").contains(modelName.value)) &&
      (localStorage.getItem(modelName.value) != null)) {
      deserialiseModel(localStorage.getItem(modelName.value))
    } else {
      errorDiv.innerHTML = ""
      errorDiv.appendChild(div(cls:="alert alert-danger")(
        s"Model '${modelName.value}' hasn't been stored locally.").render)
    }
  val saveModel = () =>
    if (modelName.value == "") {
      errorDiv.innerHTML = ""
      errorDiv.appendChild(div(cls:="alert alert-danger")(
        "You didn't provide a name for the model.").render)
    } else if (! modelName.value.contains(",")) {
      if (localStorage.getItem("models") == null) {
        localStorage.setItem("models",modelName.value.toString)
      } else if (! localStorage.getItem("models").split(",").contains(modelName.value)) {
        localStorage.setItem("models",
          localStorage.getItem("models") + "," + modelName.value)
      }
      localStorage.setItem(modelName.value,serialiseModel)
    } else {
      errorDiv.innerHTML = ""
      errorDiv.appendChild(div(cls:="alert alert-danger")(
        "Model name shouldn't contains commas.").render)
    }

  def availableModels: String =
    if (localStorage.getItem("models") != null)
      "Available models: " + localStorage.getItem("models") + "."
    else "No available models in the storage."

  val mainDiv: html.Div =
    div(cls:="container text-center")(
      // -- Title --
      // div(cls:="container",margin:=10)(h1("Fragger")),
      // TODO: Missing description after title
      // -- Rules --
      div(cls:="row",margin:=10)(h2("Rules")),
      div(cls:="row",margin:=10)(
        div(cls:="col-md-1")("name"),
        div(cls:="col-md-5")("left-hand side"),
        div(cls:="col-md-1"),
        div(cls:="col-md-5")("right-hand side")),
      ruleDiv,
      // -- Observables --
      div(cls:="row",margin:=10)(h2("Observables")),
      div(cls:="row",margin:=10)(
        div(cls:="col-md-2")("name"),
        div(cls:="col-md-10")("graph expression")),
      obsDiv,
      // -- Errors --
      errorDiv,
      // -- Buttons --
      div(cls:="row",margin:=10,
        style:="margin-top:50px; margin-bottom:20px")(
        div(cls:="col-md-2")(button(cls:="btn btn-lg btn-default",
          onclick:=addRule)("Add rule")),
          div(cls:="col-md-2")(button(cls:="btn btn-lg btn-default",
            onclick:=addObs)("Add observable")),
          div(cls:="col-md-4")(
            button(cls:="btn btn-lg btn-primary",width:="100%",
              onclick:=genEquations)("Generate equations!")),
          div(cls:="col-md-4",style:="font-size:18px; line-height:37px")(
            "Maximum number of equations: ",maxNumEqs)),
      // -- Save and load models --
      // FIXME: This should be in a side menu
      div(cls:="row",margin:=10,style:="margin-bottom:30px")(
        div(cls:="col-md-4",style:="font-size:18px; line-height:37px")(
          div(style:="float:left; margin-top:2px")("Model name: "),
          div(style:="overflow:hidden; padding-left:10px")(modelName)),
        div(cls:="col-md-2")(button(cls:="btn btn-lg btn-default",
          onclick:=loadModel)("Load model")),
        div(cls:="col-md-2")(button(cls:="btn btn-lg btn-default",
          onclick:=saveModel)("Save model")),
        div(cls:="col-md-4",
          style:="font-size:18px; line-height:37px; margin-top:2px")(
          availableModels)),
      // -- Results --
      resultDiv).render

  // localStorage.clear
  def main(): Unit = document.body.appendChild(mainDiv)
}
