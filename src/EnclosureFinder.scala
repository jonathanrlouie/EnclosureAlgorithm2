
case class Position(x: Int, y: Int)

trait GridCell {
  val pos: Position
}

case class EmptyCell(pos: Position) extends GridCell

case class FilledCell(pos: Position) extends GridCell

case class SparseGrid(cells: List[List[FilledCell]])

trait HasDenseGrid {
  val grid: Vector[Vector[Boolean]]

  def isFilled(x: Int, y: Int): Boolean = {
    try {
      grid(y)(x)
    } catch {
      case e: IndexOutOfBoundsException => false
    }
  }
}

case class Enclosure(position: Position, outline: List[Position], grid: Vector[Vector[Boolean]]) extends HasDenseGrid {
  def getPositions: List[Position] = {
    grid.zipWithIndex.flatMap{
      case (row, yIndex) =>
        row.zipWithIndex.collect{
          case (true, xIndex) => Position(xIndex, yIndex)
        }
    }.toList
  }
}

case class CellCluster(pos: Position, grid: Vector[Vector[Boolean]]) extends HasDenseGrid {
  def removeCells(cellsToRemove: List[Position]): CellCluster = {
    CellCluster(pos, cellsToRemove.foldLeft(grid)((prevGrid, pos) => {
      val rowIdxToUpdate = pos.y
      prevGrid.updated(rowIdxToUpdate, prevGrid(rowIdxToUpdate).updated(pos.x, false))
    }))
  }
}

trait Direction {
  def xOffset: Int

  def yOffset: Int
}

case object NorthWest extends Direction {
  def xOffset: Int = -1

  def yOffset: Int = -1
}

case object North extends Direction {
  def xOffset: Int = 0

  def yOffset: Int = -1
}

case object NorthEast extends Direction {
  def xOffset: Int = 1

  def yOffset: Int = -1
}

case object East extends Direction {
  def xOffset: Int = 1

  def yOffset: Int = 0
}

case object SouthEast extends Direction {
  def xOffset: Int = 1

  def yOffset: Int = 1
}

case object South extends Direction {
  def xOffset: Int = 0

  def yOffset: Int = 1
}

case object SouthWest extends Direction {
  def xOffset: Int = -1

  def yOffset: Int = 1
}

case object West extends Direction {
  def xOffset: Int = -1

  def yOffset: Int = 0
}

class EnclosureFinder {

  // algorithm that finds all cells inside of and including an outline of an enclosure
  def findEnclosureCells(enclosureOutline: List[Position]): (Position, Vector[Vector[Boolean]]) = {
    // topLeft is equivalent to the enclosure's position (analogous to cluster position)
    val (topLeft, bottomRight) = findGridCorners(enclosureOutline)
    // this is used to represent the enclosure outline in a dense grid
    val (gridWidth, gridHeight) = (bottomRight.x - topLeft.x + 1, bottomRight.y - topLeft.y + 1)
    val initGrid = Vector.fill(gridHeight, gridWidth)(false)
    val outlineGrid = enclosureOutline
      .map(pos => Position(pos.x - topLeft.x, pos.y - topLeft.y))
      .foldLeft(initGrid)((prevGrid, pos) => {
        val rowIdxToUpdate = pos.y
        prevGrid.updated(rowIdxToUpdate, prevGrid(rowIdxToUpdate).updated(pos.x, true))
      })
    val outlineCluster = CellCluster(topLeft, outlineGrid)
    val border = findBorder(topLeft, bottomRight)
    val filledGrid = Vector.fill(gridHeight, gridWidth)(true)
    (topLeft, removeOuterCells(border, filledGrid, outlineCluster))
  }

  private def findGridCorners(enclosureOutline: List[Position]): (Position, Position) = {
    enclosureOutline.tail.foldLeft(enclosureOutline.head, enclosureOutline.head) { case ((currentTopLeft, currentBottomRight), pos) =>
      val topLeftX = if (pos.x < currentTopLeft.x) {
        pos.x
      } else {
        currentTopLeft.x
      }
      val topLeftY = if (pos.y < currentTopLeft.y) {
        pos.y
      } else {
        currentTopLeft.y
      }
      val bottomRightX = if (pos.x > currentBottomRight.x) {
        pos.x
      } else {
        currentBottomRight.x
      }
      val bottomRightY = if (pos.y > currentBottomRight.y) {
        pos.y
      } else {
        currentBottomRight.y
      }
      (Position(topLeftX, topLeftY), Position(bottomRightX, bottomRightY))
    }
  }

  def findBorder(topLeft: Position, bottomRight: Position): List[Position] = {
    def listSearchPositions(currentPos: Position, direction: Direction, acc: List[Position]): List[Position] = {
      if (currentPos == topLeft) {
        currentPos :: acc
      } else {
        val nextDirection = direction match {
          case South =>
            if (currentPos.y == bottomRight.y) {
              East
            } else {
              South
            }
          case East =>
            if (currentPos.x == bottomRight.x) {
              North
            } else {
              East
            }
          case North =>
            if (currentPos.y == topLeft.y) {
              West
            } else {
              North
            }
          case West =>
            West
        }
        listSearchPositions(Position(currentPos.x + nextDirection.xOffset, currentPos.y + nextDirection.yOffset), nextDirection, currentPos :: acc)
      }
    }

    listSearchPositions(Position(topLeft.x, topLeft.y + 1), South, List())
  }

  private def removeOuterCells(border: List[Position], filledGrid: Vector[Vector[Boolean]], outlineCluster: CellCluster): Vector[Vector[Boolean]] = {
    border.foldLeft(filledGrid)((grid, pos) => searchAndRemove(grid, pos, outlineCluster))
  }

  private def searchAndRemove(grid: Vector[Vector[Boolean]], borderPosition: Position, outlineCluster: CellCluster): Vector[Vector[Boolean]] = {
    val (gridBorderPositionX, gridBorderPositionY) = (borderPosition.x - outlineCluster.pos.x, borderPosition.y - outlineCluster.pos.y)
    if (grid(gridBorderPositionY)(gridBorderPositionX) && !outlineCluster.isFilled(gridBorderPositionX, gridBorderPositionY)) {
      updateFilledGrid(Position(gridBorderPositionX, gridBorderPositionY), grid, outlineCluster, List())._1
    } else {
      grid
    }
  }

  def updateFilledGrid(currentPos: Position, grid: Vector[Vector[Boolean]], outlineCluster: CellCluster, visited: List[Position]): (Vector[Vector[Boolean]], List[Position]) = {
    if (visited.contains(currentPos) || outlineCluster.isFilled(currentPos.x, currentPos.y) || outOfBounds(currentPos, grid)) {
      (grid, visited)
    } else {
      val rowIdxToUpdate = currentPos.y
      val updatedGrid = if (!outOfBounds(currentPos, grid)) {
        grid.updated(rowIdxToUpdate, grid(rowIdxToUpdate).updated(currentPos.x, false))
      } else {
        grid
      }
      val (updatedGridE, visitedE) = updateFilledGrid(Position(currentPos.x + 1, currentPos.y), updatedGrid, outlineCluster, currentPos :: visited)
      val (updatedGridES, visitedES) = updateFilledGrid(Position(currentPos.x, currentPos.y + 1), updatedGridE, outlineCluster, visitedE)
      val (updatedGridESW, visitedESW) = updateFilledGrid(Position(currentPos.x - 1, currentPos.y), updatedGridES, outlineCluster, visitedES)
      updateFilledGrid(Position(currentPos.x, currentPos.y - 1), updatedGridESW, outlineCluster, visitedESW)

    }
  }

  def outOfBounds(position: Position, grid: Vector[Vector[Boolean]]): Boolean = {
    try {
      grid(position.y)(position.x)
      false
    } catch {
      case e: IndexOutOfBoundsException => true
    }
  }

  private def createEnclosure(cluster: CellCluster, currentPos: Position, visited: List[Position]): Enclosure = {
    val idxOfCollision = visited.indexOf(currentPos)
    val enclosureOutline = visited.take(idxOfCollision + 1).map(pos => Position(pos.x + cluster.pos.x, pos.y + cluster.pos.y))
    val (enclosurePos, enclosureCells) = findEnclosureCells(enclosureOutline)
    Enclosure(enclosurePos, enclosureOutline, enclosureCells)
  }

  private def checkDirections(
                               currentPos: Position,
                               cluster: CellCluster,
                               directionsToCheck: List[Direction],
                               visited: List[Position],
                               enclosureAcc: List[Enclosure]
                             ): (List[Enclosure], Option[Position], Option[CellCluster]) = {
    if (visited.contains(currentPos)) {
      // TODO remove everything inside of updatedCluster's enclosure as well!
      val enclosure = createEnclosure(cluster, currentPos, visited)
      val (xOffset, yOffset) = (enclosure.position.x - cluster.pos.x, enclosure.position.y - cluster.pos.y)
      val cellsToRemove = enclosure.getPositions.map(pos => Position(pos.x + xOffset, pos.y + yOffset))
      //val updatedCluster = cluster.removeCells(enclosure.cells.take(enclosure.cells.length - 1))
      val updatedCluster = cluster.removeCells(cellsToRemove)
      (enclosure :: enclosureAcc, Some(currentPos), Some(updatedCluster))
    } else {
      checkDirectionsHelper(currentPos, cluster, directionsToCheck, visited, enclosureAcc)
    }
  }

  private def checkDirectionsHelper(
                                     currentPos: Position,
                                     cluster: CellCluster,
                                     directionsToCheck: List[Direction],
                                     visited: List[Position],
                                     enclosureAcc: List[Enclosure]
                                   ): (List[Enclosure], Option[Position], Option[CellCluster]) = {
    if (directionsToCheck.isEmpty) {
      (enclosureAcc, None, None)
    } else {
      val nextDirectionToCheck = directionsToCheck.head
      if (cluster.isFilled(currentPos.x + nextDirectionToCheck.xOffset, currentPos.y + nextDirectionToCheck.yOffset)) {
        val updatedVisited = currentPos :: visited
        val nextPosition = Position(currentPos.x + nextDirectionToCheck.xOffset, currentPos.y + nextDirectionToCheck.yOffset)
        val (foundEnclosures, oCollisionPos, oUpdatedCluster) = nextDirectionToCheck match {
          case NorthWest => checkDirections(nextPosition, cluster, List(NorthEast, North, NorthWest, West, SouthWest, South), updatedVisited, enclosureAcc)
          case North => checkDirections(nextPosition, cluster, List(NorthEast, North, NorthWest, West, SouthWest), updatedVisited, enclosureAcc)
          case NorthEast => checkDirections(nextPosition, cluster, List(SouthEast, East, NorthEast, North, NorthWest, West), updatedVisited, enclosureAcc)
          case East => checkDirections(nextPosition, cluster, List(SouthEast, East, NorthEast, North, NorthWest), updatedVisited, enclosureAcc)
          case SouthEast => checkDirections(nextPosition, cluster, List(SouthWest, South, SouthEast, East, NorthEast, North), updatedVisited, enclosureAcc)
          case South => checkDirections(nextPosition, cluster, List(SouthWest, South, SouthEast, East, NorthEast), updatedVisited, enclosureAcc)
          case SouthWest => checkDirections(nextPosition, cluster, List(NorthWest, West, SouthWest, South, SouthEast, East), updatedVisited, enclosureAcc)
          case West => checkDirections(nextPosition, cluster, List(NorthWest, West, SouthWest, South, SouthEast), updatedVisited, enclosureAcc)
        }
        (oCollisionPos, oUpdatedCluster) match {
          case (Some(collisionPos), Some(updatedCluster)) if collisionPos == currentPos => checkDirectionsHelper(currentPos, updatedCluster, directionsToCheck.tail, visited, foundEnclosures)
          case (Some(collisionPos), Some(updatedCluster)) => (foundEnclosures, oCollisionPos, oUpdatedCluster)
          case _ => checkDirectionsHelper(currentPos, cluster, directionsToCheck.tail, visited, foundEnclosures)
        }
      } else {
        checkDirectionsHelper(currentPos, cluster, directionsToCheck.tail, visited, enclosureAcc)
      }
    }
  }

  private def findClusterEnclosures(cluster: CellCluster): List[Enclosure] = {
    val colIdxStart = cluster.grid.head.indexOf(true)
    val initDirections = List(SouthWest, South, SouthEast, East)
    val currentPos = Position(colIdxStart, 0)
    checkDirections(currentPos, cluster, initDirections, List(), List())._1
  }

  def findLargestEnclosures(listOfClusters: List[CellCluster]): List[Enclosure] = {
    listOfClusters.foldLeft(List[Enclosure]())(
      (acc, cluster) => findClusterEnclosures(cluster) ++ acc
    )
  }

}

object Main {
  def main(args: Array[String]): Unit = {

    val finder = new EnclosureFinder()
    val enclosures = finder.findLargestEnclosures(List(
      CellCluster(
        Position(0, 0),
        Vector(
          Vector(true, false, true, false, false, false, false, true),
          Vector(false, true, true, true, true, true, true, true),
          Vector(false, true, true, true, false, false, false, false),
          Vector(false, true, true, false, false, false, false, false)
        )
      )
    )) ++ finder.findLargestEnclosures(List(
      CellCluster(
        Position(10, 10),
        Vector(
          Vector(true, false, true, false),
          Vector(true, true, false, true),
          Vector(false, false, true, false),
          Vector(false, true, true, false)
        )
      )
    ))
    enclosures.foreach(a => println(a.outline))
  }

}