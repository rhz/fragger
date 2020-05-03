package fragger

import scala.collection.mutable
import scala.scalajs.js
import js.annotation.{JSExport,JSName}
// import js.DynamicImplicits._
// import js.Dynamic.{global => g}

import org.scalajs.dom
import dom.{document,html,localStorage}
import scalatags.JsDom.all._
// import fr.iscpif.scaladget.mapping._
// import fr.iscpif.scaladget.d3._
import org.scalajs.d3._
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

  // -- Parsing --

  object GraphParser extends Parsers with RegexParsers {

    lazy val ident: Parser[String] =
      """\w+""".r | failure("an identifier was expected")

    def addNode(g: Graph, name: N, label: Option[L], mark: Int) = {
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

    lazy val graph: Parser[Graph] =
      // rep((node <~ ";") | (edge <~ ";")) ^^ {
      repsep(edge | node | failure("a node or an edge was expected"),
        ";" | ",") <~ opt(";" |
          failure("'->' or ',' or ';' was expected")) ^^ {
        nodesAndEdges =>
        val g = Graph()()
        var i = 0
        for (nodeOrEdge <- nodesAndEdges) nodeOrEdge match {
          case Node(name,label,mark) => addNode(g,name,label,mark)
          case Edge(source,target,label) => {
            addNode(g,source.name,source.label,source.mark)
            addNode(g,target.name,target.label,target.mark)
            val e = IdDiEdge(i,source.name,target.name)
            i += 1
            g += e
            if (label.isDefined)
              g(e).label = label.get
          }
        }
        g
      }

    lazy val node: Parser[Node] =
      markedNode | inMarkedNode | outMarkedNode | unmarkedNode

    lazy val unmarkedNode: Parser[Node] = ident ~ label ^^ {
      case name ~ label => Node(name,label,0) }

    lazy val inMarkedNode: Parser[Node] = (">" ~> ident <~ "<") ~ label ^^ {
      case name ~ label => Node(name,label,1) }

    lazy val outMarkedNode: Parser[Node] = ("<" ~> ident <~ ">") ~ label ^^ {
      case name ~ label => Node(name,label,2) }

    lazy val markedNode: Parser[Node] = ("|" ~> ident <~ "|") ~ label ^^ {
      case name ~ label => Node(name,label,3) }

    lazy val edge: Parser[Edge] = node ~ arrow ~ node ^^ {
      case source ~ label ~ target => Edge(source,target,label) }

    lazy val arrow: Parser[Option[L]] =
      ("->" ~> label) | failure("'->' or ';' was expected")

    lazy val label: Parser[Option[L]] = opt("[" ~> ident <~ "]")

    sealed abstract class NodeOrEdge
    case class Node(name: N, label: Option[L], mark: Int) extends NodeOrEdge
    case class Edge(source: Node, target: Node, label: Option[L]) extends NodeOrEdge

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
      val nodes = g.nodes.zipWithIndex.toMap.mapValues(_.toString)
      val edges = (for (e <- g.edges) yield
        (e,IdDiEdge(e.id,nodes(e.source),nodes(e.target)))).toMap
      val h = Graph(nodes.values,edges.values)
      for (n <- g.inMarks) h(nodes(n)).inMark
      for (n <- g.outMarks) h(nodes(n)).outMark
      for ((n,l) <- g.nodelabels) h(nodes(n)).label = l
      for ((e,l) <- g.edgelabels) h(edges(e)).label = l
      h
    }
  }

  val cnt = utils.Counter()
  def countFrags = (g: Graph) => { cnt.next; None }

  // -- Rules and Observables --

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
      div(cls:="col-md-5")(lhs),
      div(cls:="glyphicon glyphicon-arrow-right col-md-1",
        aria.hidden:=true,style:="line-height:35px"),
      div(cls:="col-md-5")(rhs),
      div(cls:="col-md-1")(name)).render
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
  val maxNumEqs: html.Input = input(tpe:="text",size:=1,value:="10").render
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
    val os = for {
      o <- obs
      if o.name.value != ""
    } yield (o.name.value,
      GraphParser.parse(o.graph.value,errorDiv,
        s"observable '${o.name.value}'"))
    val odes = generateMeanODEs[N,L,E,L,MarkedDiGraph](
      maxNumEqs.value.toInt,rs,os.map(_._2),countFrags)
    // FIXME: Better output
    val p = ODEPrinter(odes)
    val name = new ObsNaming(os)
    val lines = for (ODE(lhs,rhs) <- p.simplify) yield (
      s"d(${name(lhs)})/dt = " + (if (rhs.isEmpty) "0" else
        rhs.terms.map(p.strMn(_,name)).mkString(" + ")))
    def toDot(g: Graph) =
      (for (n <- g.nodes) yield (
        if (g(n).inMarked && g(n).outMarked) "|" + n + "|"
        else if (g(n).inMarked) ">" + n + "<"
        else if (g(n).outMarked) "<" + n + ">"
        else n) + (g(n).label match {
          case Some(l) => "[" + l + "]"
          case None => ""
        })).mkString(", ") + (
        if (g.nodes.isEmpty || g.edges.isEmpty) "" else ", ") +
      (for (e <- g.edges.toSeq) yield
        s"${e.source}->${e.target}").mkString(", ")
    val names = for ((g,n) <- name.seq)
                yield s"$n := ${toDot(g)}"
    resultDiv.innerHTML = ""
    resultDiv.appendChild(
      div(cls:="row",margin:=10)(h2("Results")).render)
    resultDiv.appendChild(
      textarea(style:="margin-bottom:50px; width:100%; height:" +
      // TODO: Try to find a more general way to handle long lines
      ((names.size + lines.size + 1 + lines.filter(_.length > 130).size) * 30) + "px")(
      names.mkString("\n") + "\n\n" + lines.mkString("\n")).render)
  }

  // -- Serialisation --

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
    s"{rules:[$rs],observables:[$os],maxEqs:${maxNumEqs.value}}"
  }

  val Model = ("""{\s*rules\s*:\s*\[\s*(.*)\s*\]\s*,\s*observables""" +
    """\s*:\s*\[\s*(.*)\s*\]\s*,\s*maxEqs\s*:\s*(.*)\s*}""").r
  val Triple = """\(\s*"(.*)"\s*,\s*"(.*)"\s*,\s*"(.*)"\s*\)""".r
  val Twople = """\(\s*"(.*)"\s*,\s*"(.*)"\s*\)""".r
  def deserialiseModel(in: String) = in match {
    case Model(rs,os,maxEqs) => {
      maxNumEqs.value = maxEqs
      rules.clear
      obs.clear
      ruleDiv.innerHTML = ""
      obsDiv.innerHTML = ""
      for (Triple(name,lhs,rhs) <- rs.split(";")) {
        ruleDiv.appendChild(newRule)
        val RuleInput(n,l,r) = rules.last
        n.value = name
        l.value = lhs
        r.value = rhs
      }
      for (Twople(name,graph) <- os.split(";")) {
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

  // -- Loading and Saving models --

  val infile: html.Input = input(tpe:="file",onchange:=(() => {
    val reader = new dom.FileReader
    reader.onload = (e: dom.UIEvent) => {
      deserialiseModel(reader.result.asInstanceOf[String]) }
    reader.readAsText(infile.files(0)) })).render
  var modelName: String = "model"

  def availableModels: Seq[String] =
    if (localStorage.getItem("models") != null)
      localStorage.getItem("models").split(",")
    else Seq()

  def loadModel(modelName: String) =
    if (localStorage.getItem(modelName) != null) {
      this.modelName = modelName
      deserialiseModel(localStorage.getItem(modelName))
    } else {
      errorDiv.innerHTML = ""
      errorDiv.appendChild(div(cls:="alert alert-danger")(
        s"Model '$modelName' is not stored in the browser.").render)
    }

  val loadFromFile = () => infile.click()

  def loadModelList: html.UList =
    ul(cls:="dropdown-menu",aria.labelledby:="loadModel")(
      li(a(href:="#",onclick:=loadFromFile)("From file")),
      li(role:="separator",cls:="divider"),
      li(cls:="dropdown-header")("From browser"),
      for (m <- availableModels) yield
        li(a(href:="#",onclick:=(() => loadModel(m)))(m))).render

  def saveModel(modelName: String) =
    if (modelName.value.contains(",")) {
      errorDiv.innerHTML = ""
      errorDiv.appendChild(div(cls:="alert alert-danger")(
        "Model name shouldn't contains commas.").render)
    } else {
      this.modelName = modelName
      localStorage.setItem(modelName,serialiseModel)
      if (localStorage.getItem("models") == null) {
        localStorage.setItem("models",modelName.value.toString)
      } else if (! localStorage.getItem("models").split(",").contains(
        modelName.value)) {
        localStorage.setItem("models",
          localStorage.getItem("models") + "," + modelName.value)
      }
    }

  @JSName("Blob")
  class Blob(parts: js.Array[String], tpe: js.Dynamic)
      extends js.Object {
    def size: Int = js.native
    def `type`: String = js.native
  }

  val saveToFile = () => {
    val file = new Blob(js.Array(serialiseModel),
      js.Dynamic.literal("type" -> "text/plain;charset=utf8"))
    js.Dynamic.global.saveAs(file,modelName + ".json")
  }

  def saveModelList: html.UList = {
    val modelName = input(tpe:="text",width:="70%").render
    ul(cls:="dropdown-menu",aria.labelledby:="saveModel")(
      li(a(href:="#",onclick:=saveToFile)("To file")),
      li(role:="separator",cls:="divider"),
      li(cls:="dropdown-header")("To browser"),
      for (m <- availableModels) yield
        li(a(href:="#",onclick:=(() => saveModel(m)))(m)),
      li(a(href:="#")(modelName,
        button(cls:="btn btn-xs btn-default glyphicon glyphicon-ok",
          style:="margin-left:10px; margin-bottom:6px",
          onclick:=(() => saveModel(modelName.value)))))).render
  }

  // -- HTML --

  val mainDiv: html.Div =
    div(cls:="container text-center",id:="main-div")(
      // -- Title --
      // div(cls:="row",margin:=10)(h1("Fragger")),
      // TODO: Missing description after title
      // -- Rules --
      div(cls:="row",margin:=10)(h2("Rules")),
      div(cls:="row",margin:=10)(
        div(cls:="col-md-5")("left-hand side"),
        div(cls:="col-md-1"),
        div(cls:="col-md-5")("right-hand side"),
        div(cls:="col-md-1")("rate")),
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
        div(cls:="col-md-2")(
          button(cls:="btn btn-lg btn-default",
            onclick:=addRule)("Add rule")),
        div(cls:="col-md-2")(
          button(cls:="btn btn-lg btn-default",
            onclick:=addObs)("Add observable")),
        div(cls:="col-md-4")(
          button(cls:="btn btn-lg btn-primary",width:="100%",
            onclick:=genEquations)("Generate equations!")),
        // -- Save and load models --
        // TODO: Move to side menu (offcanvas plugin) or navbar
        div(cls:="col-md-2")(
          div(cls:="dropdown",style:="display:inline-block")(
            button(cls:="btn btn-lg btn-default dropdown-toggle",
              id:="loadModel",data.toggle:="dropdown",
              aria.haspopup:="true",aria.expanded:="true")(
              "Load model ",span(cls:="caret")),
            loadModelList)),
        div(cls:="col-md-2")(
          div(cls:="dropdown",style:="display:inline-block")(
            button(cls:="btn btn-lg btn-default dropdown-toggle",
              id:="saveModel",data.toggle:="dropdown",
              aria.haspopup:="true",aria.expanded:="true")(
              "Save model ",span(cls:="caret")),
            saveModelList))),
      // div(cls:="row",margin:=10,
      //   style:="margin-top:50px; margin-bottom:20px")(
      //   div(cls:="btn-toolbar",role:="toolbar")(
      //     // div(cls:="btn-group",role:="group")(
      //     div(cls:="btn-group",role:="group")(
      //       button(cls:="btn btn-lg btn-default",
      //         onclick:=addRule)("Add rule")),
      //     div(cls:="btn-group",role:="group")(
      //       button(cls:="btn btn-lg btn-default",
      //         onclick:=addObs)("Add observable")),
      //     div(cls:="btn-group",role:="group")(
      //       button(cls:="btn btn-lg btn-primary",width:="100%",
      //         onclick:=genEquations)("Generate equations!")),
      //     // -- Save and load models --
      //     // TODO: Move to side menu (offcanvas plugin) or navbar
      //     div(cls:="btn-group",role:="group")(
      //       div(cls:="dropdown",style:="display:inline-block")(
      //         button(cls:="btn btn-lg btn-default dropdown-toggle",id:="loadModel",
      //           data.toggle:="dropdown",aria.haspopup:="true",aria.expanded:="true")(
      //           "Load model ",span(cls:="caret")),
      //         loadModelList)),
      //     div(cls:="btn-group",role:="group")(
      //       div(cls:="dropdown",style:="display:inline-block")(
      //         button(cls:="btn btn-lg btn-default dropdown-toggle",id:="saveModel",
      //           data.toggle:="dropdown",aria.haspopup:="true",aria.expanded:="true")(
      //           "Save model ",span(cls:="caret")),
      //         saveModelList)))),
      div(cls:="row",style:="margin-bottom:50px")( //,style:="font-size:18px; line-height:37px")(
        "Maximum number of equations: ",maxNumEqs),
      // -- Results --
      resultDiv).render


  // -- Graph drawings --

  // class Node(val nme: String)
  //     extends Layout.GraphNode {
  //   var name = nme
  // }
  // object Node {
  //   def apply(name: String) = new Node(name)
  // }
  // class Edge(override var source: Layout.GraphNode,
  //            override var target: Layout.GraphNode)
  //     extends Layout.GraphLink
  // object Edge {
  //   def apply(source: Layout.GraphNode,
  //             target: Layout.GraphNode) = new Edge(source,target)
  // }

  // trait GraphElement {
  //   def literal: js.Dynamic
  // }
  // val lit = js.Dynamic.literal
  // class Node(val id: String) extends GraphElement {
  //   def literal = lit("id" -> id, "title" -> id)
  // }
  // class Edge(val source: Node,
  //            val target: Node) extends GraphElement {
  //   def literal = lit("source" -> source.literal,
  //                     "target" -> target.literal)
  // }

  // Example: http://bl.ocks.org/mbostock/1153292
  // val links = Array(
  //   new Edge(new Node("Microsoft"),new Node("Amazon")))
    // lit(source = "Microsoft", target = "HTC", `type` = "licensing"),
    // lit(source = "Samsung", target = "Apple", `type` = "suit"),
    // lit(source = "Motorola", target = "Apple", `type` = "suit"),
    // lit(source = "Nokia", target = "Apple", `type` = "resolved"),
    // lit(source = "HTC", target = "Apple", `type` = "suit"),
    // lit(source = "Kodak", target = "Apple", `type` = "suit"),
    // lit(source = "Microsoft", target = "Barnes & Noble", `type` = "suit"),
    // lit(source = "Microsoft", target = "Foxconn", `type` = "suit"),
    // lit(source = "Oracle", target = "Google", `type` = "suit"),
    // lit(source = "Apple", target = "HTC", `type` = "suit"),
    // lit(source = "Microsoft", target = "Inventec", `type` = "suit"),
    // lit(source = "Samsung", target = "Kodak", `type` = "resolved"),
    // lit(source = "LG", target = "Kodak", `type` = "resolved"),
    // lit(source = "RIM", target = "Kodak", `type` = "suit"),
    // lit(source = "Sony", target = "LG", `type` = "suit"),
    // lit(source = "Kodak", target = "LG", `type` = "resolved"),
    // lit(source = "Apple", target = "Nokia", `type` = "resolved"),
    // lit(source = "Qualcomm", target = "Nokia", `type` = "resolved"),
    // lit(source = "Apple", target = "Motorola", `type` = "suit"),
    // lit(source = "Microsoft", target = "Motorola", `type` = "suit"),
    // lit(source = "Motorola", target = "Microsoft", `type` = "suit"),
    // lit(source = "Huawei", target = "ZTE", `type` = "suit"),
    // lit(source = "Ericsson", target = "ZTE", `type` = "suit"),
    // lit(source = "Kodak", target = "Samsung", `type` = "resolved"),
    // lit(source = "Apple", target = "Samsung", `type` = "suit"),
    // lit(source = "Kodak", target = "RIM", `type` = "suit"),
    // lit(source = "Nokia", target = "Qualcomm", `type` = "suit"))

  // val nodes = Array(new Node("Microsoft"),new Node("Amazon"))
  // val (w,h) = (960,500)
  // import js.JSConverters._
  // val force = d3.layout.force()
  //   .nodes(nodes.map(_.literal).toJSArray.asInstanceOf[js.Array[Layout.GraphNode]])
  //   .links(links.map(_.literal).toJSArray.asInstanceOf[js.Array[Layout.GraphLink]])
  //   .size(js.Array[Double](w,h))
  //   .linkDistance(60)
  //   .charge(-300)
  //   // .on("tick", tick)
  //   .start();
  // val svg = d3.select("main-div").append("svg")
  //   .attr("width",w)
  //   .attr("height",h);

  // val links: List[(String,String,String)] = List(
  //   ("Microsoft", "Amazon", "licensing"),
  //   ("Microsoft", "HTC", "licensing"),
  //   ("Samsung", "Apple", "suit"),
  //   ("Motorola", "Apple", "suit"),
  //   ("Nokia", "Apple", "resolved"),
  //   ("HTC", "Apple", "suit"),
  //   ("Kodak", "Apple", "suit"),
  //   ("Microsoft", "Barnes & Noble", "suit"),
  //   ("Microsoft", "Foxconn", "suit"),
  //   ("Oracle", "Google", "suit"),
  //   ("Apple", "HTC", "suit"),
  //   ("Microsoft", "Inventec", "suit"),
  //   ("Samsung", "Kodak", "resolved"),
  //   ("LG", "Kodak", "resolved"),
  //   ("RIM", "Kodak", "suit"),
  //   ("Sony", "LG", "suit"),
  //   ("Kodak", "LG", "resolved"),
  //   ("Apple", "Nokia", "resolved"),
  //   ("Qualcomm", "Nokia", "resolved"),
  //   ("Apple", "Motorola", "suit"),
  //   ("Microsoft", "Motorola", "suit"),
  //   ("Motorola", "Microsoft", "suit"),
  //   ("Huawei", "ZTE", "suit"),
  //   ("Ericsson", "ZTE", "suit"),
  //   ("Kodak", "Samsung", "resolved"),
  //   ("Apple", "Samsung", "suit"),
  //   ("Kodak", "RIM", "suit"),
  //   ("Nokia", "Qualcomm", "suit"))

  // val svg = d3.select("main-div")
  //   .append("svg")
  //   .attr("width", "800px")
  //   .attr("height", "800px")
  // val svgG = svg.append("g").classed("graph", true)
  // val dragLine = svgG.append("svg:path")
  //   .attr("class", "link dragline hidden")
  //   .attr("d", "M0,0L0,0")
  //   .style("marker-end", "url(#mark-end-arrow)")
  // val defs = svg.append("svg:defs") // why svg instead of svgG?
  // val pathRoot = svgG.append("g")
  // val circleRoot = svgG.append("g")

  // -- Main --

  def main(): Unit = document.body.appendChild(mainDiv)
  // localStorage.clear
}
