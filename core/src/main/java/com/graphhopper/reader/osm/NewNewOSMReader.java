/*
 *  Licensed to GraphHopper GmbH under one or more contributor
 *  license agreements. See the NOTICE file distributed with this work for
 *  additional information regarding copyright ownership.
 *
 *  GraphHopper GmbH licenses this file to you under the Apache License,
 *  Version 2.0 (the "License"); you may not use this file except in
 *  compliance with the License. You may obtain a copy of the License at
 *
 *       http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */

package com.graphhopper.reader.osm;

import com.carrotsearch.hppc.*;
import com.carrotsearch.hppc.cursors.LongCursor;
import com.graphhopper.coll.GHIntLongHashMap;
import com.graphhopper.coll.GHLongHashSet;
import com.graphhopper.coll.GHLongIntBTree;
import com.graphhopper.reader.*;
import com.graphhopper.reader.dem.EdgeSampling;
import com.graphhopper.reader.dem.ElevationProvider;
import com.graphhopper.reader.dem.GraphElevationSmoothing;
import com.graphhopper.routing.OSMReaderConfig;
import com.graphhopper.routing.ev.Country;
import com.graphhopper.routing.util.AreaIndex;
import com.graphhopper.routing.util.CustomArea;
import com.graphhopper.routing.util.EncodingManager;
import com.graphhopper.routing.util.countryrules.CountryRule;
import com.graphhopper.routing.util.countryrules.CountryRuleFactory;
import com.graphhopper.routing.util.parsers.TurnCostParser;
import com.graphhopper.storage.*;
import com.graphhopper.util.*;
import com.graphhopper.util.shapes.GHPoint;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.xml.stream.XMLStreamException;
import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import static com.graphhopper.reader.osm.OSMReader.createTurnRelations;
import static com.graphhopper.util.Helper.nf;
import static java.util.Collections.emptyList;
import static java.util.Collections.emptyMap;

public class NewNewOSMReader {
    private static final Logger LOGGER = LoggerFactory.getLogger(NewNewOSMReader.class);
    private static final int END_NODE = 0;
    private static final int CONNECTION_NODE = 1;
    private static final int JUNCTION_NODE = 2;
    private static final int INTERMEDIATE_NODE = 3;

    private final OSMReaderConfig config;
    private final EncodingManager encodingManager;
    private ElevationProvider elevationProvider = ElevationProvider.NOOP;
    private AreaIndex<CustomArea> areaIndex;
    private CountryRuleFactory countryRuleFactory = null;
    private GHLongIntBTree nodePointersByOSMNodeIds;
    private DataAccess nodeEntries;
    // todonow: keeping the reader relations here should be ok memory-wise as long as we only keep those related to
    //          our routes and skip restrictions. we should also clear the member list of each relation. and should we
    //          use the ReaderRelation type?
    private final LongObjectMap<List<ReaderRelation>> osmRelationsByWayID = new LongObjectScatterMap<>();
    private GHLongHashSet osmWayIdSet = new GHLongHashSet();
    private IntLongMap edgeIdToOsmWayIdMap = new GHIntLongHashMap();

    private final GraphHopperStorage graph;
    private final TurnCostStorage tcs;

    public NewNewOSMReader(GraphHopperStorage graph, OSMReaderConfig config, EncodingManager encodingManager) {
        this.graph = graph;
        this.config = config;
        this.encodingManager = encodingManager;
        this.nodePointersByOSMNodeIds = new GHLongIntBTree(200);
        this.nodeEntries = new RAMDirectory().create("", DAType.RAM_INT, 1 << 20);
        this.nodeEntries.create(100);
        tcs = graph.getTurnCostStorage();
    }

    public void readOSM(File file) {
        if (!file.exists())
            throw new IllegalArgumentException("The OSM file does not exist: " + file.getAbsolutePath());

        LOGGER.info("Start reading OSM file: '" + file + "'");
        LOGGER.info("pass1 - start");
        StopWatch swPass1 = StopWatch.started();
        readOSM(file, new Pass1Handler());
        LOGGER.info("pass1 - finished, took: {}", swPass1.stop().getTimeString());

        LOGGER.info("pass2 - start");
        StopWatch swPass2 = StopWatch.started();
        readOSM(file, new Pass2Handler(areaIndex, countryRuleFactory));
        LOGGER.info("pass1 - finished, took: {}", swPass2.stop().getTimeString());

        LOGGER.info("Finished reading OSM file." +
                " pass1: " + (int) swPass1.getSeconds() + "s" +
                " pass2: " + (int) swPass2.getSeconds() + "s" +
                " total: " + (int) (swPass1.getSeconds() + swPass2.getSeconds()) + "s");
    }

    private void readOSM(File file, ReaderElementHandler handler) {
        try (OSMInput osmInput = openOsmInputFile(file)) {
            ReaderElement elem;
            while ((elem = osmInput.getNext()) != null) {
                handler.handleElement(elem);
            }
            handler.onFinish();
        } catch (Exception e) {
            throw new RuntimeException("Could not parse OSM file: " + file.getAbsolutePath(), e);
        }
    }

    void setNodeCoordinates(int nodePointer, int latInt, int lonInt, int tagIndex) {
        if (tagIndex >= (1 << 29))
            throw new IllegalArgumentException("Maximum node tag index exceeded");
        long pointer = (nodePointer + Integer.MAX_VALUE);
        nodeEntries.setInt(pointer * 16L + 4L, latInt);
        nodeEntries.setInt(pointer * 16L + 8L, lonInt);
        int nodeType = nodeEntries.getInt(pointer * 16L + 12L) & 0x3;
        nodeEntries.setInt(pointer * 16L + 12L, tagIndex << 2 | nodeType);
    }

    public NewNewOSMReader setAreaIndex(AreaIndex<CustomArea> areaIndex) {
        this.areaIndex = areaIndex;
        return this;
    }

    public NewNewOSMReader setElevationProvider(ElevationProvider elevationProvider) {
        this.elevationProvider = elevationProvider;
        return this;
    }

    public NewNewOSMReader setCountryRuleFactory(CountryRuleFactory ruleFactory) {
        this.countryRuleFactory = ruleFactory;
        return this;
    }

    private class Pass1Handler implements ReaderElementHandler {
        private boolean handledWays;
        private long wayCounter = -1;
        private long relationsCounter = -1;
        private long relevantRelationsCounter = -1;
        private long metaRelationsCounter = -1;
        private long restrictionRelationsCounter = -1;
        private long acceptedWays = 0;
        private int nextNodePointer = Integer.MIN_VALUE + 1;
        private final LongSet wayIds = new LongScatterSet();
        private final LongSet wayIdsWithRestrictions = new LongScatterSet();

        @Override
        public void handleWay(ReaderWay way) {
            if (!handledWays)
                LOGGER.info("pass1 - start reading OSM ways");
            handledWays = true;

            if (++wayCounter % 10_000_000 == 0)
                LOGGER.info("pass1 - processed ways: " + nf(wayCounter) + ", " + Helper.getMemInfo());

            if (!acceptWay(way))
                return;
            acceptedWays++;

            for (LongCursor node : way.getNodes()) {
                final boolean isEnd = node.index == 0 || node.index == way.getNodes().size() - 1;
                int nodePointer = nodePointersByOSMNodeIds.get(node.value);
                if (nodePointer == Integer.MIN_VALUE) {
                    nodePointer = nextNodePointer++;
                    nodePointersByOSMNodeIds.put(node.value, nodePointer);
                    int nodeType = isEnd ? END_NODE : INTERMEDIATE_NODE;
                    setNodeEntry(nodePointer, nodeType, Integer.MAX_VALUE, Integer.MAX_VALUE, -1);
                } else {
                    int prevNodeType = getNodeType(nodePointer);
                    if (prevNodeType == END_NODE && isEnd) {
                        setNodeType(nodePointer, CONNECTION_NODE);
                    } else {
                        setNodeType(nodePointer, JUNCTION_NODE);
                    }
                }
            }
            // we keep track of all the ways we keep so we can later ignore OSM relations that do not include any
            // ways of interest
            wayIds.add(way.getId());
        }

        @Override
        public void handleRelation(ReaderRelation relation) {
            if (++relationsCounter % 1_000_000 == 0)
                LOGGER.info("pass1 - processed relations: " + nf(relationsCounter) + ", " + Helper.getMemInfo());
            if (relation.isMetaRelation())
                ++metaRelationsCounter;
            if (relation.hasTag("type", "restriction")) {
                ++restrictionRelationsCounter;
                relation.getMembers().forEach(m -> wayIdsWithRestrictions.add(m.getRef()));
            }
            boolean relevant = relation.getMembers().stream().map(ReaderRelation.Member::getRef).anyMatch(wayIds::contains);
            if (relevant)
                ++relevantRelationsCounter;

            if (relation.hasTag("type", "restriction")) {
                // we keep the osm way ids that occur in turn relations, because this way we know for which GH edges
                // we need to remember the associated osm way id
                List<OSMTurnRelation> turnRelations = createTurnRelations(relation);
                for (OSMTurnRelation turnRelation : turnRelations) {
                    osmWayIdSet.add(turnRelation.getOsmIdFrom());
                    osmWayIdSet.add(turnRelation.getOsmIdTo());
                }
            } else if (!relation.isMetaRelation() && relation.hasTag("type", "route")) {
                // todonow: should we keep others than 'route'?
                for (ReaderRelation.Member member : relation.getMembers()) {
                    // we only support members that reference at least one of the ways we are interested in
                    if (member.getType() == ReaderRelation.Member.WAY && wayIds.contains(member.getRef())) {
                        List<ReaderRelation> relations = osmRelationsByWayID.get(member.getRef());
                        if (relations == null) {
                            relations = new ArrayList<>();
                            osmRelationsByWayID.put(member.getRef(), relations);
                        }
                        relations.add(relation);
                    }
                }
            }

        }

        private void setNodeType(int nodePointer, int nodeType) {
            if (nodeType < 0 || nodeType >= 4)
                throw new IllegalArgumentException("invalid nodeType: " + nodeType);
            long pointer = nodePointer + Integer.MAX_VALUE;
            int tagIndex = nodeEntries.getInt(pointer * 16L + 12L) >> 2;
            nodeEntries.setInt(pointer * 16L + 12L, tagIndex << 2 | nodeType);
        }

        @Override
        public void onFinish() {
            LOGGER.info("pass1 - accepted ways: " + nf(acceptedWays) + ", wayIds: " + wayIds.size() + ", wayIds for restrictions " + wayIdsWithRestrictions.size() + ", way nodes: " + nf(nodePointersByOSMNodeIds.getSize()) + ", relations: " + nf(relationsCounter) + ", relevant relations: " + nf(relevantRelationsCounter) + ", meta relations: " + nf(metaRelationsCounter) + ", restriction relations: " + nf(restrictionRelationsCounter));
        }
    }

    private void setNodeEntry(int nodePointer, int nodeType, int latInt, int lonInt, int tagIndex) {
        if (tagIndex >= (1 << 29))
            throw new IllegalArgumentException("Maximum node tag index exceeded");
        long pointer = (nodePointer + Integer.MAX_VALUE);
        nodeEntries.ensureCapacity((pointer + 1) * 16L);
        nodeEntries.setInt(pointer * 16L, -1);
        nodeEntries.setInt(pointer * 16L + 4L, latInt);
        nodeEntries.setInt(pointer * 16L + 8L, lonInt);
        nodeEntries.setInt(pointer * 16L + 12L, tagIndex << 2 | nodeType);
    }

    private void setGHId(int nodePointer, int ghId) {
        long pointer = nodePointer + Integer.MAX_VALUE;
        nodeEntries.setInt(pointer * 16L, ghId);
    }

    private int getGHId(int nodePointer) {
        long pointer = nodePointer + Integer.MAX_VALUE;
        return nodeEntries.getInt(pointer * 16L);
    }

    private int getNodeType(int nodePointer) {
        long pointer = nodePointer + Integer.MAX_VALUE;
        return nodeEntries.getInt(pointer * 16L + 12L) & 0x3;
    }

    private boolean acceptWay(ReaderWay way) {
        if (way.getNodes().size() < 2 || !way.hasTags())
            return false;
        return encodingManager.acceptWay(way, new EncodingManager.AcceptWay());
    }

    private class Pass2Handler implements ReaderElementHandler {
        private boolean handledNodes;
        private boolean handledWays;
        private final List<Map<String, Object>> nodeTags = new ArrayList<>();
        private long foundNodes = 0;
        private long nodeCounter = -1;
        private long wayCounter = -1;
        private final LongSet handledBarriers = new LongHashSet();
        private final LongIntScatterMap extraNodeTowerNodes = new LongIntScatterMap();
        private long newUniqueOsmId = -Long.MAX_VALUE;

        private long barrierCount = 0;
        private long ignoredBarriersCounter = 0;
        private long edgeCount = 0;
        private int nextTowerId = -1;

        private final DistanceCalc distCalc = DistanceCalcEarth.DIST_EARTH;
        private final boolean doSimplify;
        private final DouglasPeucker simplifyAlgo = new DouglasPeucker();
        private final AreaIndex<CustomArea> areaIndex;
        private final CountryRuleFactory countryRuleFactory;
        private long zeroCounter = 0;

        public Pass2Handler(AreaIndex<CustomArea> areaIndex, CountryRuleFactory countryRuleFactory) {
            this.areaIndex = areaIndex;
            this.countryRuleFactory = countryRuleFactory;
            doSimplify = config.getMaxWayPointDistance() > 0;
            simplifyAlgo.setMaxDistance(config.getMaxWayPointDistance());
            simplifyAlgo.setElevationMaxDistance(config.getElevationMaxWayPointDistance());
        }

        @Override
        public void handleNode(ReaderNode node) {
            if (!handledNodes)
                LOGGER.info("pass2 - start reading OSM nodes");
            handledNodes = true;
            if (handledWays)
                throw new IllegalStateException("OSM node elements must be located before way elements in OSM file");

            if (++nodeCounter % 10_000_000 == 0)
                LOGGER.info("pass2 - processed nodes: " + nf(nodeCounter) +
                        ", accepted nodes: " + nf(foundNodes) + ", " + Helper.getMemInfo());

            int nodePointer = nodePointersByOSMNodeIds.get(node.getId());
            if (nodePointer == Integer.MIN_VALUE)
                return;
            foundNodes++;
            Map<String, Object> tags = node.getTags();
            int tagIndex = -1;
            if (!tags.isEmpty()) {
                nodeTags.add(tags);
                tagIndex = nodeTags.size() - 1;
            }
            setNodeCoordinates(nodePointer,
                    Helper.degreeToInt(node.getLat()),
                    Helper.degreeToInt(node.getLon()),
                    tagIndex);
        }

        @Override
        public void handleWay(ReaderWay way) {
            if (!handledWays)
                LOGGER.info("pass2 - start reading OSM ways");
            handledWays = true;

            if (++wayCounter % 10_000_000 == 0)
                LOGGER.info("pass2 - processed ways: " + nf(wayCounter) + ", " + Helper.getMemInfo());

            if (!acceptWay(way))
                return;

            setArtificialWayTags(way);
            List<ReaderRelation> relations = osmRelationsByWayID.get(way.getId());
            if (relations == null)
                relations = Collections.emptyList();

            List<ReaderNode> segment = new ArrayList<>();
            for (LongCursor node : way.getNodes()) {
                int nodePointer = nodePointersByOSMNodeIds.get(node.value);
                if (nodePointer == Integer.MIN_VALUE)
                    // todonow
                    throw new IllegalStateException("todonow missing node");
                ReaderNode readerNode = getReaderNode(nodePointer, node.value);
                if (encodingManager.handleNodeTags(readerNode) > 0)
                    barrierCount++;
                boolean isBarrier = !handledBarriers.contains(node.value) && encodingManager.handleNodeTags(readerNode) > 0;
                int nodeType = getNodeType(nodePointer);
                if (readerNode.getLat() == Double.MAX_VALUE) {
                    // this node exists in ways, but not in nodes. we ignore it, but we split edges when we encounter
                    // such a missing node. for example an OSM way might lead out an area where nodes are available and
                    // back into it. we do not want to connect the exit/entry points using a straight line. this usually
                    // should only happen for OSM extracts.
                    if (segment.size() > 1) {
                        handleSegment(segment, way, relations);
                        segment = new ArrayList<>();
                    }
                } else if (nodeType == JUNCTION_NODE) {
                    if (isBarrier) {
                        LOGGER.warn("OSM node {} at {},{} is a barrier node at a junction, the barrier will be ignored", node.value, readerNode.getLat(), readerNode.getLon());
                        // from now on we ignore this barrier (no further warnings, but also no extra barrier edges)
                        handledBarriers.add(node.value);
                        ignoredBarriersCounter++;
                    }
                    if (!segment.isEmpty()) {
                        segment.add(readerNode);
                        handleSegment(segment, way, relations);
                        segment = new ArrayList<>();
                    }
                    segment.add(readerNode);
                } else {
                    segment.add(readerNode);
                }
            }
            // the last segment might end at the end of the way
            if (segment.size() > 1)
                handleSegment(segment, way, relations);
        }

        @Override
        public void handleRelation(ReaderRelation relation) {
            if (tcs != null && relation.hasTag("type", "restriction")) {
                TurnCostParser.ExternalInternalMap map = new TurnCostParser.ExternalInternalMap() {
                    @Override
                    public int getInternalNodeIdOfOsmNode(long nodeOsmId) {
                        if (nodeOsmId < 0) {
                            return extraNodeTowerNodes.get(nodeOsmId);
                        } else
                            return getGHId(nodePointersByOSMNodeIds.get(nodeOsmId));
                    }

                    @Override
                    public long getOsmIdOfInternalEdge(int edgeId) {
                        return edgeIdToOsmWayIdMap.get(edgeId);
                    }
                };
                List<OSMTurnRelation> turnRelations = createTurnRelations(relation);
                for (OSMTurnRelation turnRelation : turnRelations) {
                    long osmId = turnRelation.getViaOsmNodeId();
                    int viaNode = map.getInternalNodeIdOfOsmNode(osmId);
                    if (viaNode >= 0) {
                        encodingManager.handleTurnRelationTags(turnRelation, map, graph);
                    }
                }
            }
        }

        private void handleSegment(List<ReaderNode> segment, ReaderWay way, List<ReaderRelation> relations) {
            if (segment.size() < 2)
                throw new IllegalArgumentException("Segment size must be >= 2");
            boolean isLoop = segment.get(0).getId() == segment.get(segment.size() - 1).getId();
            if (segment.size() == 2 && isLoop) {
                LOGGER.warn("Loop in OSM way: {} will be ignored, duplicate node: {} at {},{}",
                        way.getId(), segment.get(0).getId(), segment.get(0).getLat(), segment.get(0).getLon());
                return;
            }
            if (isLoop) {
                handleSegmentWithBarriers(segment.subList(0, segment.size() - 1), way, relations);
                handleSegmentWithBarriers(segment.subList(segment.size() - 2, segment.size()), way, relations);
            } else {
                handleSegmentWithBarriers(segment, way, relations);
            }
        }

        private void handleSegmentWithBarriers(final List<ReaderNode> parentSegment, ReaderWay way, List<ReaderRelation> relations) {
            List<ReaderNode> segment = new ArrayList<>();
            for (int i = 0; i < parentSegment.size(); i++) {
                ReaderNode node = parentSegment.get(i);
                boolean isBarrier = !handledBarriers.contains(node.getId()) && encodingManager.handleNodeTags(node) > 0;
                if (isBarrier) {
                    // we only handle each barrier once. it might appear at the beginning/end of two ways for example,
                    // and we only want to add *one* barrier edge. this way we also prevent multiple barrier edges at
                    // real junctions, even though they should not exist according to OSM mapping rules (but do exist
                    // anyway)
                    handledBarriers.add(node.getId());
                    // todonow: create artificial osm id?
                    long newId = ++newUniqueOsmId;
                    ReaderNode extraNode = new ReaderNode(newId, node.getLat(), node.getLon());
                    if (!segment.isEmpty()) {
                        // the segment up to the barrier
                        segment.add(node);
                        handleSegmentFinal(segment, way, relations);
                        segment = new ArrayList<>();
                    }
                    // barrier segment, make sure the extra node is not at the end of the segment
                    if (i == parentSegment.size() - 1) {
                        segment.add(extraNode);
                        segment.add(node);
                    } else {
                        segment.add(node);
                        segment.add(extraNode);
                    }
                    // todonow: make it a 'barrier'
                    handleSegmentFinal(segment, way, relations);
                    segment = new ArrayList<>();
                    segment.add(extraNode);
                } else {
                    segment.add(node);
                }
            }
            if (segment.size() > 1)
                handleSegmentFinal(segment, way, relations);
        }

        private void handleSegmentFinal(List<ReaderNode> segment, ReaderWay way, List<ReaderRelation> relations) {
            // no more loops or missing nodes, already split at barrier nodes and connects two tower nodes
            // -> first and last nodes are tower nodes and the others are geometry
            edgeCount++;
            int fromGHId;
            if (segment.get(0).getId() < 0) {
                if (extraNodeTowerNodes.containsKey(segment.get(0).getId()))
                    fromGHId = extraNodeTowerNodes.get(segment.get(0).getId());
                else {
                    fromGHId = ++nextTowerId;
                    extraNodeTowerNodes.put(segment.get(0).getId(), fromGHId);
                    graph.getNodeAccess().setNode(fromGHId, segment.get(0).getLat(), segment.get(0).getLon(), elevationProvider.getEle(segment.get(0)));
                }
            } else {
                int fromNodePointer = nodePointersByOSMNodeIds.get(segment.get(0).getId());
                fromGHId = getGHId(fromNodePointer);
                if (fromGHId < 0) {
                    fromGHId = ++nextTowerId;
                    setGHId(fromNodePointer, fromGHId);
                    graph.getNodeAccess().setNode(fromGHId, segment.get(0).getLat(), segment.get(0).getLon(), elevationProvider.getEle(segment.get(0)));
                }
            }

            int toGHId;
            if (segment.get(segment.size() - 1).getId() < 0) {
                if (extraNodeTowerNodes.containsKey(segment.get(segment.size() - 1).getId()))
                    toGHId = extraNodeTowerNodes.get(segment.get(segment.size() - 1).getId());
                else {
                    toGHId = ++nextTowerId;
                    extraNodeTowerNodes.put(segment.get(segment.size() - 1).getId(), toGHId);
                    graph.getNodeAccess().setNode(toGHId, segment.get(segment.size() - 1).getLat(), segment.get(segment.size() - 1).getLon(), elevationProvider.getEle(segment.get(segment.size() - 1)));
                }
            } else {
                int toNodePointerId = nodePointersByOSMNodeIds.get(segment.get(segment.size() - 1).getId());
                toGHId = getGHId(toNodePointerId);
                if (toGHId < 0) {
                    toGHId = ++nextTowerId;
                    setGHId(toNodePointerId, toGHId);
                    graph.getNodeAccess().setNode(toGHId, segment.get(segment.size() - 1).getLat(), segment.get(segment.size() - 1).getLon(), elevationProvider.getEle(segment.get(segment.size() - 1)));
                }
            }
            IntsRef relFlags = encodingManager.createRelationFlags();
            for (ReaderRelation relation : relations) {
                relFlags = encodingManager.handleRelationTags(relation, relFlags);
            }

            EncodingManager.AcceptWay acceptWay = new EncodingManager.AcceptWay();
            encodingManager.acceptWay(way, acceptWay);
            IntsRef edgeFlags = encodingManager.handleWayTags(way, acceptWay, relFlags);
            if (edgeFlags.isEmpty())
                return;

            PointList pointList = new PointList(segment.size(), graph.getNodeAccess().is3D());
            for (ReaderNode node : segment)
                pointList.add(node.getLat(), node.getLon(), elevationProvider.getEle(node));

            // Smooth the elevation before calculating the distance because the distance will be incorrect if calculated afterwards
            if (config.isSmoothElevation())
                GraphElevationSmoothing.smoothElevation(pointList);

            // sample points along long edges
            if (config.getLongEdgeSamplingDistance() < Double.MAX_VALUE && pointList.is3D())
                pointList = EdgeSampling.sample(pointList, config.getLongEdgeSamplingDistance(), distCalc, elevationProvider);

            if (doSimplify && pointList.size() > 2)
                simplifyAlgo.simplify(pointList);

            double towerNodeDistance = distCalc.calcDistance(pointList);
            if (towerNodeDistance < 0.001) {
                // As investigation shows often two paths should have crossed via one identical point
                // but end up in two very close points.
                zeroCounter++;
                towerNodeDistance = 0.001;
            }
            double maxDistance = (Integer.MAX_VALUE - 1) / 1000d;
            if (Double.isNaN(towerNodeDistance)) {
                LOGGER.warn("Bug in OSM or GraphHopper. Illegal tower node distance " + towerNodeDistance + " reset to 1m, osm way " + way.getId());
                towerNodeDistance = 1;
            }
            if (Double.isInfinite(towerNodeDistance) || towerNodeDistance > maxDistance) {
                // Too large is very rare and often the wrong tagging. See #435
                // so we can avoid the complexity of splitting the way for now (new towernodes would be required, splitting up geometry etc)
                LOGGER.warn("Bug in OSM or GraphHopper. Too big tower node distance " + towerNodeDistance + " reset to large value, osm way " + way.getId());
                towerNodeDistance = maxDistance;
            }

            EdgeIteratorState edgeState = graph.edge(fromGHId, toGHId).setDistance(towerNodeDistance).setFlags(edgeFlags);
            // If the entire way is just the first and last point, do not waste space storing an empty way geometry
            if (pointList.size() > 2) {
                // the geometry consists only of pillar nodes, but we check that the first and last points of the pointList
                // are equal to the tower node coordinates
                checkCoordinates(fromGHId, pointList.get(0));
                checkCoordinates(toGHId, pointList.get(pointList.size() - 1));
                // tower node coordinates are not included in way geometry
                edgeState.setWayGeometry(pointList.shallowCopy(1, pointList.size() - 1, false));
            }
            encodingManager.applyWayTags(way, edgeState);
            checkDistance(edgeState);
            storeOsmWayID(edgeState.getEdge(), way.getId());
        }

        private void storeOsmWayID(int edgeId, long osmWayId) {
            if (osmWayIdSet.contains(osmWayId))
                edgeIdToOsmWayIdMap.put(edgeId, osmWayId);
        }

        private void checkCoordinates(int nodeIndex, GHPoint point) {
            final NodeAccess nodeAccess = graph.getNodeAccess();
            final double tolerance = 1.e-6;
            if (Math.abs(nodeAccess.getLat(nodeIndex) - point.getLat()) > tolerance || Math.abs(nodeAccess.getLon(nodeIndex) - point.getLon()) > tolerance)
                throw new IllegalStateException("Suspicious coordinates for node " + nodeIndex + ": (" + nodeAccess.getLat(nodeIndex) + "," + nodeAccess.getLon(nodeIndex) + ") vs. (" + point + ")");
        }

        private void checkDistance(EdgeIteratorState edge) {
            final double tolerance = 1;
            final double edgeDistance = edge.getDistance();
            final double geometryDistance = distCalc.calcDistance(edge.fetchWayGeometry(FetchMode.ALL));
            if (edgeDistance > 2_000_000)
                LOGGER.warn("Very long edge detected: " + edge + " dist: " + edgeDistance);
            else if (Math.abs(edgeDistance - geometryDistance) > tolerance)
                throw new IllegalStateException("Suspicious distance for edge: " + edge + " " + edgeDistance + " vs. " + geometryDistance
                        + ", difference: " + (edgeDistance - geometryDistance));
        }

        private ReaderNode getReaderNode(int nodePointer, long osmId) {
            long pointer = nodePointer + Integer.MAX_VALUE;
            int tagIndex = nodeEntries.getInt(pointer * 16L + 12L) >> 2;
            return new ReaderNode(osmId,
                    Helper.intToDegree(nodeEntries.getInt(pointer * 16L + 4L)),
                    Helper.intToDegree(nodeEntries.getInt(pointer * 16L + 8L)),
                    tagIndex > -1 ? nodeTags.get(tagIndex) : emptyMap()
            );
        }

        @Override
        public void onFinish() {
            LOGGER.info("pass2 - found {} nodes, with tags: {}, barriers: {}, ignored barriers at junctions: {}, nodes: {}, edges: {}", nf(foundNodes), nf(nodeTags.size()), nf(barrierCount), nf(ignoredBarriersCounter), nf(nextTowerId + 1), nf(edgeCount));
        }

        private void setArtificialWayTags(ReaderWay way) {
            // TODO move this after we have created the edge and know the coordinates => encodingManager.applyWayTags
            LongArrayList osmNodeIds = way.getNodes();
            // Estimate length of ways containing a route tag e.g. for ferry speed calculation
            ReaderNode first = getTmpReaderNode(osmNodeIds.get(0));
            ReaderNode last = getTmpReaderNode(osmNodeIds.get(osmNodeIds.size() - 1));
            double firstLat = first.getLat(), firstLon = last.getLon();
            double lastLat = last.getLat(), lastLon = last.getLon();
            GHPoint estimatedCenter = null;
            if (!Double.isNaN(firstLat) && !Double.isNaN(firstLon) && !Double.isNaN(lastLat) && !Double.isNaN(lastLon)) {
                double estimatedDist = distCalc.calcDist(firstLat, firstLon, lastLat, lastLon);
                // Add artificial tag for the estimated distance and center
                way.setTag("estimated_distance", estimatedDist);
                estimatedCenter = new GHPoint((firstLat + lastLat) / 2, (firstLon + lastLon) / 2);
                way.setTag("estimated_center", estimatedCenter);
            }

            if (way.getTag("duration") != null) {
                try {
                    long dur = OSMReaderUtility.parseDuration(way.getTag("duration"));
                    // Provide the duration value in seconds in an artificial graphhopper specific tag:
                    way.setTag("duration:seconds", Long.toString(dur));
                } catch (Exception ex) {
                    LOGGER.warn("Parsing error in way with OSMID=" + way.getId() + " : " + ex.getMessage());
                }
            }

            List<CustomArea> customAreas = estimatedCenter == null || areaIndex == null
                    ? emptyList()
                    : areaIndex.query(estimatedCenter.lat, estimatedCenter.lon);
            // special handling for countries: since they are built-in with GraphHopper they are always fed to the encodingmanager
            Country country = Country.MISSING;
            for (CustomArea customArea : customAreas) {
                Object countryCode = customArea.getProperties().get("ISO3166-1:alpha3");
                if (countryCode == null)
                    continue;
                if (country != Country.MISSING)
                    LOGGER.warn("Multiple countries found for way {}: {}, {}", way.getId(), country, countryCode);
                country = Country.valueOf(countryCode.toString());
            }
            way.setTag("country", country);

            if (countryRuleFactory != null) {
                CountryRule countryRule = countryRuleFactory.getCountryRule(country);
                if (countryRule != null)
                    way.setTag("country_rule", countryRule);
            }

            // also add all custom areas as artificial tag
            way.setTag("custom_areas", customAreas);
        }

        private ReaderNode getTmpReaderNode(long osmId) {
            int nodePointer = nodePointersByOSMNodeIds.get(osmId);
            if (nodePointer == Integer.MIN_VALUE)
                // todonow
                throw new IllegalStateException("todonow missing node");
            return getReaderNode(nodePointer, osmId);
        }
    }

    private interface ReaderElementHandler {
        default void handleElement(ReaderElement elem) {
            switch (elem.getType()) {
                case ReaderElement.NODE:
                    handleNode((ReaderNode) elem);
                    break;
                case ReaderElement.WAY:
                    handleWay((ReaderWay) elem);
                    break;
                case ReaderElement.RELATION:
                    handleRelation((ReaderRelation) elem);
                    break;
                case ReaderElement.FILEHEADER:
                    handleFileHeader((OSMFileHeader) elem);
                    break;
                default:
                    throw new IllegalStateException("Unknown reader element type: " + elem.getType());
            }
        }

        default void handleNode(ReaderNode node) {
        }

        default void handleWay(ReaderWay way) {
        }

        default void handleRelation(ReaderRelation relation) {
        }

        default void handleFileHeader(OSMFileHeader fileHeader) {
        }

        default void onFinish() {
        }
    }

    private OSMInput openOsmInputFile(File file) throws IOException, XMLStreamException {
        return new OSMInputFile(file).setWorkerThreads(config.getWorkerThreads()).open();
    }

}