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

package com.graphhopper.gtfs;

import com.conveyal.gtfs.model.DBConnection;
import com.conveyal.gtfs.model.Transfer;
import com.graphhopper.GraphHopper;
import com.graphhopper.GraphHopperConfig;
import com.graphhopper.routing.ev.Subnetwork;
import com.graphhopper.routing.querygraph.QueryGraph;
import com.graphhopper.routing.util.DefaultSnapFilter;
import com.graphhopper.routing.weighting.Weighting;
import com.graphhopper.storage.index.InMemConstructionIndex;
import com.graphhopper.storage.index.IndexStructureInfo;
import com.graphhopper.storage.index.LineIntIndex;
import com.graphhopper.util.EdgeIteratorState;
import com.graphhopper.util.PMap;
import com.graphhopper.util.shapes.BBox;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.File;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.time.Duration;
import java.time.Instant;
import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class GraphHopperGtfs extends GraphHopper {

    private static final Logger LOGGER = LoggerFactory.getLogger(GraphHopperGtfs.class);

    private final GraphHopperConfig ghConfig;
    private GtfsStorage gtfsStorage;
    private PtGraph ptGraph;

    public GraphHopperGtfs(GraphHopperConfig ghConfig) {
        this.ghConfig = ghConfig;
    }

    @Override
    protected void importOSM() {
        if (ghConfig.has("datareader.file")) {
            super.importOSM();
        } else {
            createBaseGraphAndProperties();
        }
    }

    @Override
    protected void importPublicTransit() {
        ptGraph = new PtGraph(getBaseGraph().getDirectory(), 100);
        gtfsStorage = new GtfsStorage(getBaseGraph().getDirectory());
        LineIntIndex stopIndex = new LineIntIndex(new BBox(-180.0, 180.0, -90.0, 90.0), getBaseGraph().getDirectory(), "stop_index");
        if (getGtfsStorage().loadExisting()) {
            ptGraph.loadExisting();
            stopIndex.loadExisting();
        } else {
            ensureWriteAccess();
            getGtfsStorage().create();
            ptGraph.create(100);
            InMemConstructionIndex indexBuilder = new InMemConstructionIndex(IndexStructureInfo.create(
                    new BBox(-180.0, 180.0, -90.0, 90.0), 300));
            try {
                if (ghConfig.getBool("load.from.db.validated",false)) {

                    String[] company_array = get_validated_companies();
                    for (String company_id : company_array) {
                        getGtfsStorage().loadGtfsFromDB("gtfs_" + company_id, company_id);

                    }
                }

                else if (ghConfig.getBool("load.from.db",false)) {
                    if (ghConfig.has("company.id")) {
                        String companies = ghConfig.getString("company.id", "");
                        String[] company_array = companies.split(",", -1);
                        for (String company_id : company_array) {
                            getGtfsStorage().loadGtfsFromDB("gtfs_" + company_id, company_id);
                        }
                    }
                    else {
                        throw new RuntimeException("No company id, please provide one");
                    }
                }
                else {
                    int idx = 0;
                    List<String> gtfsFiles = ghConfig.has("gtfs.file") ? Arrays.asList(ghConfig.getString("gtfs.file", "").split(",")) : Collections.emptyList();
                    for (String gtfsFile : gtfsFiles) {
                            getGtfsStorage().loadGtfsFromZipFileOrDirectory("gtfs_" + idx++, new File(gtfsFile));
                        }
                }
                getGtfsStorage().postInit();
                Map<String, Transfers> allTransfers = new HashMap<>();
                HashMap<String, GtfsReader> allReaders = new HashMap<>();
                getGtfsStorage().getGtfsFeeds().forEach((id, gtfsFeed) -> {
                    Transfers transfers = new Transfers(gtfsFeed);
                    allTransfers.put(id, transfers);
                    GtfsReader gtfsReader = new GtfsReader(id, ptGraph, ptGraph, getGtfsStorage(), getLocationIndex(), transfers, indexBuilder);
                    // Stops must be connected to the networks of all the modes
                    List<DefaultSnapFilter> snapFilters = getProfiles().stream().map(p ->
                            new DefaultSnapFilter(createWeighting(p, new PMap()), getEncodingManager().getBooleanEncodedValue(Subnetwork.key(p.getName())))).collect(Collectors.toList());
                    gtfsReader.connectStopsToStreetNetwork(e -> {
                        for (DefaultSnapFilter snapFilter : snapFilters) {
                            if (!snapFilter.accept(e))
                                return false;
                        }
                        return true;
                    });
                    LOGGER.info("Building transit graph for feed {}", gtfsFeed.feedId);
                    gtfsReader.buildPtNetwork();
                    allReaders.put(id, gtfsReader);
                });
                interpolateTransfers(allReaders, allTransfers);
            } catch (Exception e) {
                throw new RuntimeException("Error while constructing transit network. Is your GTFS file valid? Please check log for possible causes.", e);
            }
            ptGraph.flush();
            getGtfsStorage().flush();
            stopIndex.store(indexBuilder);
            stopIndex.flush();
        }
        gtfsStorage.setStopIndex(stopIndex);
        gtfsStorage.setPtGraph(ptGraph);
    }

    private String[] get_validated_companies() throws SQLException {

        DBConnection conn_user_data = new DBConnection("user_data");
        ResultSet company_id_with_tokens_rs = conn_user_data.ExecuteQuery("SELECT tokens.company_id FROM user_data.api_tokens as tokens where tokens.api_name = 'get_directions' AND tokens.revoked = 0 UNION SELECT company_id FROM working_data.info as info where info.share_gtfs='1' and info.is_airline=0;");

        DBConnection conn_working_data = new DBConnection("working_data");
        ResultSet company_id_with_gtfs_rs = conn_working_data.ExecuteQuery("SELECT company_id FROM working_data.info as info where info.validated = 1 AND info.published = 1;");

        List<String> company_id_with_tokens = new ArrayList<>();
        List<String> company_id_with_gtfs = new ArrayList<>();

        // Fetch each row from the result set
        while (company_id_with_tokens_rs.next()) {
            String company_id = company_id_with_tokens_rs.getString("company_id");
            company_id_with_tokens.add(company_id);
        }

        while (company_id_with_gtfs_rs.next()) {
            String company_id = company_id_with_gtfs_rs.getString("company_id");
            company_id_with_gtfs.add(company_id);
        }

        Set<String> company_ids = company_id_with_tokens.stream().distinct().filter(company_id_with_gtfs::contains).collect(Collectors.toSet());

        String[] company_ids_array = company_ids.toArray(new String[0]);

        return company_ids_array;

    }

    private void interpolateTransfers(HashMap<String, GtfsReader> readers, Map<String, Transfers> allTransfers) {
        LOGGER.info("Looking for transfers");
        final int maxTransferWalkTimeSeconds = ghConfig.getInt("gtfs.max_transfer_interpolation_walk_time_seconds", 120);
        QueryGraph queryGraph = QueryGraph.create(getBaseGraph(), Collections.emptyList());
        Weighting transferWeighting = createWeighting(getProfile("foot"), new PMap());
        final GraphExplorer graphExplorer = new GraphExplorer(queryGraph, ptGraph, transferWeighting, getGtfsStorage(), RealtimeFeed.empty(), true, true, false, 5.0, false, 0);
        getGtfsStorage().getStationNodes().values().stream().distinct().map(n -> new Label.NodeId(gtfsStorage.getPtToStreet().getOrDefault(n, -1), n)).forEach(stationNode -> {
            MultiCriteriaLabelSetting router = new MultiCriteriaLabelSetting(graphExplorer, true, false, false, 0, new ArrayList<>());
            router.setLimitStreetTime(Duration.ofSeconds(maxTransferWalkTimeSeconds).toMillis());
            for (Label label : router.calcLabels(stationNode, Instant.ofEpochMilli(0))) {
                if (label.parent != null) {
                    if (label.edge.getType() == GtfsStorage.EdgeType.EXIT_PT) {
                        GtfsStorage.PlatformDescriptor fromPlatformDescriptor = label.edge.getPlatformDescriptor();
                        Transfers transfers = allTransfers.get(fromPlatformDescriptor.feed_id);
                        for (PtGraph.PtEdge ptEdge : ptGraph.edgesAround(stationNode.ptNode)) {
                            if (ptEdge.getType() == GtfsStorage.EdgeType.ENTER_PT) {
                                GtfsStorage.PlatformDescriptor toPlatformDescriptor = ptEdge.getAttrs().platformDescriptor;
                                LOGGER.debug(fromPlatformDescriptor + " -> " + toPlatformDescriptor);
                                if (!toPlatformDescriptor.feed_id.equals(fromPlatformDescriptor.feed_id)) {
                                    LOGGER.debug(" Different feed. Inserting transfer with " + (int) (label.streetTime / 1000L) + " s.");
                                    insertInterpolatedTransfer(label, toPlatformDescriptor, readers);
                                } else {
                                    List<Transfer> transfersToStop = transfers.getTransfersToStop(toPlatformDescriptor.stop_id, routeIdOrNull(toPlatformDescriptor));
                                    if (transfersToStop.stream().noneMatch(t -> t.from_stop_id.equals(fromPlatformDescriptor.stop_id))) {
                                        LOGGER.debug("  Inserting transfer with " + (int) (label.streetTime / 1000L) + " s.");
                                        insertInterpolatedTransfer(label, toPlatformDescriptor, readers);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        });
    }

    private void insertInterpolatedTransfer(Label label, GtfsStorage.PlatformDescriptor toPlatformDescriptor, HashMap<String, GtfsReader> readers) {
        GtfsReader toFeedReader = readers.get(toPlatformDescriptor.feed_id);
        List<Integer> transferEdgeIds = toFeedReader.insertTransferEdges(label.node.ptNode, (int) (label.streetTime / 1000L), toPlatformDescriptor);
        List<Label.Transition> transitions = Label.getTransitions(label.parent, true);
        int[] skippedEdgesForTransfer = transitions.stream().filter(t -> t.edge != null).mapToInt(t -> {
            Label.NodeId adjNode = t.label.node;
            EdgeIteratorState edgeIteratorState = getBaseGraph().getEdgeIteratorState(t.edge.getId(), adjNode.streetNode);
            return edgeIteratorState.getEdgeKey();
        }).toArray();
        if (skippedEdgesForTransfer.length > 0) { // TODO: Elsewhere, we distinguish empty path ("at" a node) from no path
            assert isValidPath(skippedEdgesForTransfer);
            for (Integer transferEdgeId : transferEdgeIds) {
                gtfsStorage.getSkippedEdgesForTransfer().put(transferEdgeId, skippedEdgesForTransfer);
            }
        }
    }

    private boolean isValidPath(int[] edgeKeys) {
        List<EdgeIteratorState> edges = Arrays.stream(edgeKeys).mapToObj(i -> getBaseGraph().getEdgeIteratorStateForKey(i)).collect(Collectors.toList());
        for (int i = 1; i < edges.size(); i++) {
            if (edges.get(i).getBaseNode() != edges.get(i - 1).getAdjNode())
                return false;
        }
        TripFromLabel tripFromLabel = new TripFromLabel(getBaseGraph(), getEncodingManager(), gtfsStorage, RealtimeFeed.empty(), getPathDetailsBuilderFactory(), 6.0);
        tripFromLabel.transferPath(edgeKeys, createWeighting(getProfile("foot"), new PMap()), 0L);
        return true;
    }

    private String routeIdOrNull(GtfsStorage.PlatformDescriptor platformDescriptor) {
        if (platformDescriptor instanceof GtfsStorage.RouteTypePlatform) {
            return null;
        } else {
            return ((GtfsStorage.RoutePlatform) platformDescriptor).route_id;
        }
    }

    @Override
    public void close() {
        getGtfsStorage().close();
        super.close();
    }

    public GtfsStorage getGtfsStorage() {
        return gtfsStorage;
    }

    public PtGraph getPtGraph() {
        return ptGraph;
    }
}
